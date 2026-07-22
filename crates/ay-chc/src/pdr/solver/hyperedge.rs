// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Hyperedge counterexample detection via must-summary intersection.
//!
//! #1518: For hyperedge queries (multiple body predicates like P(x) ∧ Q(y) → false),
//! standard POB traceback cannot detect UNSAFE because reaching init for one body
//! predicate doesn't prove the query is violated. This module implements reach_fact
//! intersection: if ALL body predicates have init-reachable must-summaries, we check
//! if they can combine to violate the query constraint.
//!
//! Also handles the case where a query has a single body predicate (R) but R is
//! defined by a hyperedge clause like `P(x) ∧ Q(y) → R(x,y)`. In this case, we
//! trace through the hyperedge to check if P and Q's must-summaries can combine
//! to satisfy the query constraint on R.
//!
//! ## Phase 0: UNSAT-sufficient hyperedge inductiveness (#1852)
//!
//! For self-loop hyperedge clauses (predicate H appears in a clause body with other
//! predicates), we implement "UNSAT-sufficient" checking: treat other body predicates
//! as unconstrained (true) and only include the self-loop predicate's invariant.
//!
//! If the resulting weaker query is UNSAT, the clause is provably inductive.
//! If SAT, we return Unknown (conservative) since we dropped constraints.

use super::PdrSolver;
use crate::pdr::counterexample::Counterexample;
use crate::pdr::reach_fact::{ReachFact, ReachFactId};
use crate::smt::{SmtResult, SmtValue};
use crate::{ChcExpr, ChcSort, ChcVar, HornClause, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

/// Result of building a Phase 0 hyperedge inductiveness query.
pub(in crate::pdr::solver) struct HyperedgeInductiveQuery {
    /// The query formula to check (SAT means NOT inductive, UNSAT means inductive)
    pub query: ChcExpr,
    /// Candidate applied to the self-loop body predicate.
    pub candidate_on_body: ChcExpr,
    /// Interpreted clause constraint shared with the linear inductiveness path.
    pub clause_constraint: ChcExpr,
    /// Negated candidate applied to the head predicate.
    pub violated_on_head: ChcExpr,
    /// True if we dropped constraints from other body predicates (SAT is inconclusive)
    pub missing_product_state: bool,
}

impl PdrSolver {
    /// Check if a query can be proven UNSAFE via hyperedge must-summary intersection.
    ///
    /// Handles two cases:
    /// 1. Direct hyperedge query: `P(x) ∧ Q(y) → false` with constraint
    /// 2. Indirect via hyperedge rule: Query is `R(x,y) ∧ constraint → false`
    ///    and R is defined by hyperedge `P(x) ∧ Q(y) → R(x,y)`
    ///
    /// For both cases: If all body predicates have must-summaries at level 0,
    /// we check if they can combine to satisfy the query constraint.
    ///
    /// Returns Some(cex) if UNSAFE is proven, None otherwise.
    ///
    /// #1518: Implements reach_fact intersection for hyperedge UNSAFE detection.
    pub(in crate::pdr::solver) fn check_hyperedge_unsafe(
        &mut self,
        query: &HornClause,
        query_clause_index: usize,
    ) -> Option<Counterexample> {
        // Case 1: Direct hyperedge query (multiple body predicates)
        if query.body.predicates.len() > 1 {
            return self.check_direct_hyperedge_unsafe(query, query_clause_index);
        }

        // Case 2: Query on predicate R that may be defined by hyperedge clauses
        if query.body.predicates.len() == 1 {
            return self.check_indirect_hyperedge_unsafe(query, query_clause_index);
        }

        None
    }

    /// Check if a direct hyperedge query can be proven UNSAFE.
    ///
    /// For a query clause like `P(x) ∧ Q(y) → false` with constraint `x + y >= 15`:
    /// If both P and Q have must-summaries at level 0 (init-reachable), we check if
    /// `must_P(x) ∧ must_Q(y) ∧ constraint(x, y)` is SAT.
    fn check_direct_hyperedge_unsafe(
        &mut self,
        query: &HornClause,
        query_clause_index: usize,
    ) -> Option<Counterexample> {
        // Must have multiple body predicates
        if query.body.predicates.len() <= 1 {
            return None;
        }

        // Collect BACKED must-summaries for all body predicates across ALL levels
        // #1518: Check all levels to capture propagated must-summaries
        // #2247: Use backed-only summaries for proof-critical UNSAFE detection
        let mut body_summaries: Vec<ChcExpr> = Vec::new();
        for (pred, args) in &query.body.predicates {
            let must_summary = self
                .reachability
                .must_summaries
                .get_all_levels_backed(*pred)?;
            // Apply must-summary to body arguments
            let applied = self.apply_to_args(*pred, &must_summary, args)?;
            body_summaries.push(applied);
        }

        // All body predicates have must-summaries
        // Build query: must_P(x) ∧ must_Q(y) ∧ ... ∧ query_constraint
        let query_constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

        let mut components = body_summaries;
        components.push(query_constraint);

        let check_formula = self.bound_int_vars(ChcExpr::and_all(components));
        // #7984: Use persistent executor backend for integer arithmetic.

        match self.check_sat_via_executor_backend(&check_formula) {
            SmtResult::Sat(model) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Hyperedge UNSAFE detected via must-summary intersection (clause={})",
                        query_clause_index
                    );
                    safe_eprintln!("PDR: Model: {:?}", model);
                }

                // Build counterexample using reach_facts from must-summaries
                // Create reach_facts for each body predicate at level 0
                let mut premise_ids: Vec<ReachFactId> = Vec::new();
                for (pred, args) in &query.body.predicates {
                    // Extract concrete state from model for this predicate
                    let canonical_vars = self.canonical_vars(*pred).unwrap_or(&[]);
                    let concrete_parts: Vec<ChcExpr> =
                        Self::extract_concrete_state(args, canonical_vars, &model);
                    let concrete_state = if concrete_parts.is_empty() {
                        ChcExpr::Bool(true)
                    } else {
                        ChcExpr::and_all(concrete_parts)
                    };

                    // Add as reach_fact at level 0
                    let rf_id = Self::insert_reach_fact_bounded(
                        &mut self.reachability,
                        self.config.verbose,
                        ReachFact {
                            id: ReachFactId(0),
                            predicate: *pred,
                            level: 0,
                            state: concrete_state.clone(),
                            incoming_clause: None, // Init fact
                            premises: vec![],
                            instances: model.clone(),
                        },
                    )?;
                    premise_ids.push(rf_id);
                }

                // Create a synthetic "violation" reach_fact for the hyperedge query
                // This represents the query predicate (false) being reached
                // We use predicate index 0 as a placeholder since query head is false
                let violation_rf_id = Self::insert_reach_fact_bounded(
                    &mut self.reachability,
                    self.config.verbose,
                    ReachFact {
                        id: ReachFactId(0),
                        predicate: query.body.predicates[0].0, // Use first body pred as representative
                        level: 1,                              // One step above init
                        state: ChcExpr::Bool(false),           // Represents violation
                        incoming_clause: Some(query_clause_index),
                        premises: premise_ids,
                        instances: model,
                    },
                )?;

                self.build_cex_from_reach_facts(violation_rf_id, Some(query_clause_index))
            }
            // SOUNDNESS NOTE (#2659): Unknown → None is conservative. This is an early
            // Unsafe detection shortcut via must-summary intersection. If Unknown, PDR's
            // main POB-driven loop will still find the counterexample through normal
            // clause processing.
            _ => None,
        }
    }

    /// Check if a query on predicate R can be proven UNSAFE via hyperedge rules.
    ///
    /// For a query like `R(x,y) ∧ (x + y >= 15) → false` where R is defined by
    /// a hyperedge clause `P(x) ∧ Q(y) → R(x,y)`:
    /// If both P and Q have must-summaries at level 0, we check if
    /// `must_P(x) ∧ must_Q(y) ∧ (x + y >= 15)` is SAT.
    ///
    /// #1518: Implements hyperedge UNSAFE detection for indirect hyperedge queries.
    fn check_indirect_hyperedge_unsafe(
        &mut self,
        query: &HornClause,
        query_clause_index: usize,
    ) -> Option<Counterexample> {
        // Must have exactly one body predicate
        if query.body.predicates.len() != 1 {
            return None;
        }

        let (query_pred, query_args) = &query.body.predicates[0];
        let query_constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

        // Find hyperedge clauses that define query_pred
        let hyperedge_clauses: Vec<(usize, HornClause)> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, c)| {
                if let crate::ClauseHead::Predicate(head_pred, _) = &c.head {
                    // Is this a clause that defines our query predicate with multiple body preds?
                    *head_pred == *query_pred && c.body.predicates.len() > 1
                } else {
                    false
                }
            })
            .map(|(i, c)| (i, c.clone()))
            .collect();

        if hyperedge_clauses.is_empty() {
            return None;
        }

        // Try each hyperedge clause
        for (hyperedge_clause_index, hyperedge) in &hyperedge_clauses {
            if let Some(cex) = self.try_hyperedge_clause(
                query,
                query_clause_index,
                hyperedge,
                *hyperedge_clause_index,
                query_args,
                &query_constraint,
            ) {
                return Some(cex);
            }
        }

        None
    }

    /// Try to prove UNSAFE via a specific hyperedge clause.
    ///
    /// Given:
    /// - Query: `R(x,y) ∧ constraint → false`
    /// - Hyperedge: `P(a) ∧ Q(b) → R(f(a,b), g(a,b))` (or just `R(a,b)`)
    ///
    /// We need to:
    /// 1. Collect must-summaries for all body predicates (P, Q) at level 0
    /// 2. Substitute hyperedge head args into query constraint
    /// 3. Check if `must_P(a) ∧ must_Q(b) ∧ constraint[x:=f(a,b), y:=g(a,b)]` is SAT
    fn try_hyperedge_clause(
        &mut self,
        query: &HornClause,
        query_clause_index: usize,
        hyperedge: &HornClause,
        hyperedge_clause_index: usize,
        query_args: &[ChcExpr],
        query_constraint: &ChcExpr,
    ) -> Option<Counterexample> {
        // Get the head arguments from the hyperedge clause
        let hyperedge_head_args = match &hyperedge.head {
            crate::ClauseHead::Predicate(_, args) => args,
            crate::ClauseHead::False => return None,
        };

        // Collect BACKED must-summaries for all body predicates across ALL levels
        // #1518: Check all levels to capture propagated must-summaries
        // #2247: Use backed-only summaries for proof-critical UNSAFE detection
        let mut body_summaries: Vec<ChcExpr> = Vec::new();
        for (pred, args) in &hyperedge.body.predicates {
            let must_summary = self
                .reachability
                .must_summaries
                .get_all_levels_backed(*pred)?;
            // Apply must-summary to body arguments
            let applied = self.apply_to_args(*pred, &must_summary, args)?;
            body_summaries.push(applied);
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Checking hyperedge clause {} with {} must-summaries (all levels)",
                hyperedge_clause_index,
                body_summaries.len()
            );
        }

        // Build substitution from query args to hyperedge head args
        // query_args[i] = expr  →  we substitute that variable with hyperedge_head_args[i]
        let mut subst_pairs: Vec<(ChcVar, ChcExpr)> = Vec::new();
        for (i, query_arg) in query_args.iter().enumerate() {
            if let Some(hyperedge_arg) = hyperedge_head_args.get(i) {
                // If query_arg is a variable, substitute it
                if let ChcExpr::Var(var) = query_arg {
                    subst_pairs.push((var.clone(), hyperedge_arg.clone()));
                }
            }
        }
        let substituted_constraint = query_constraint.substitute(&subst_pairs);

        // Also include hyperedge body constraint if any
        if let Some(ref hc) = hyperedge.body.constraint {
            body_summaries.push(hc.clone());
        }

        // Build check formula
        let mut components = body_summaries;
        components.push(substituted_constraint);

        let check_formula = self.bound_int_vars(ChcExpr::and_all(components));
        // #7984: Use persistent executor backend for integer arithmetic.

        match self.check_sat_via_executor_backend(&check_formula) {
            SmtResult::Sat(model) => {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Indirect hyperedge UNSAFE detected via clause {}",
                        hyperedge_clause_index
                    );
                    safe_eprintln!("PDR: Model: {:?}", model);
                }

                // Build counterexample
                // Create reach_facts for each hyperedge body predicate at level 0
                let mut premise_ids: Vec<ReachFactId> = Vec::new();
                for (pred, args) in &hyperedge.body.predicates {
                    let canonical_vars = self.canonical_vars(*pred).unwrap_or(&[]);
                    let concrete_parts: Vec<ChcExpr> =
                        Self::extract_concrete_state(args, canonical_vars, &model);
                    let concrete_state = if concrete_parts.is_empty() {
                        ChcExpr::Bool(true)
                    } else {
                        ChcExpr::and_all(concrete_parts)
                    };

                    let rf_id = Self::insert_reach_fact_bounded(
                        &mut self.reachability,
                        self.config.verbose,
                        ReachFact {
                            id: ReachFactId(0),
                            predicate: *pred,
                            level: 0,
                            state: concrete_state,
                            incoming_clause: None, // Init fact
                            premises: vec![],
                            instances: model.clone(),
                        },
                    )?;
                    premise_ids.push(rf_id);
                }

                // Create reach_fact for R (the hyperedge head) at level 1
                let r_rf_id = Self::insert_reach_fact_bounded(
                    &mut self.reachability,
                    self.config.verbose,
                    ReachFact {
                        id: ReachFactId(0),
                        predicate: query.body.predicates[0].0,
                        level: 1,
                        state: ChcExpr::Bool(true), // R is reached
                        incoming_clause: Some(hyperedge_clause_index),
                        premises: premise_ids,
                        instances: model.clone(),
                    },
                )?;

                // Create final violation reach_fact at level 2 (query violation)
                let violation_rf_id = Self::insert_reach_fact_bounded(
                    &mut self.reachability,
                    self.config.verbose,
                    ReachFact {
                        id: ReachFactId(0),
                        predicate: query.body.predicates[0].0,
                        level: 2,
                        state: ChcExpr::Bool(false), // Violation
                        incoming_clause: Some(query_clause_index),
                        premises: vec![r_rf_id],
                        instances: model,
                    },
                )?;

                self.build_cex_from_reach_facts(violation_rf_id, Some(query_clause_index))
            }
            // SOUNDNESS NOTE (#2659): Unknown → None is conservative. Indirect hyperedge
            // detection is an early Unsafe shortcut. The main POB loop handles the general case.
            _ => None,
        }
    }

    /// Build a Phase 0 hyperedge inductiveness query for a self-loop clause.
    ///
    /// #1852: For a hyperedge clause `B1(a1) ∧ B2(a2) ∧ ... ∧ H(body_h) ∧ c ⇒ H(head_h)`
    /// where `H` is the predicate we're checking inductiveness for:
    ///
    /// Phase 0 builds: `candidate_H(body_h) ∧ c ∧ ¬candidate_H(head_h)`
    ///
    /// This drops any constraints on other body predicates (B1, B2, etc.), treating them
    /// as unconstrained (true). The result is a weaker query:
    ///
    /// - If UNSAT: The clause preserves the candidate even with maximally weak environment.
    ///   This is a sound "inductive" result.
    /// - If SAT: The model may be spurious (due to dropped constraints). Return as
    ///   `missing_product_state = true` to signal inconclusive result.
    ///
    /// Returns None if the clause has no self-loop occurrence of `predicate`.
    pub(in crate::pdr::solver) fn build_hyperedge_inductive_query(
        &mut self,
        clause: &HornClause,
        predicate: PredicateId,
        candidate: &ChcExpr,
    ) -> Option<HyperedgeInductiveQuery> {
        // Must be a hyperedge (multiple body predicates)
        if clause.body.predicates.len() <= 1 {
            return None;
        }

        // Find self-loop occurrence: body predicate matching head predicate
        let self_loop_entry = clause
            .body
            .predicates
            .iter()
            .find(|(bp, _)| *bp == predicate)?;
        let body_args = &self_loop_entry.1;

        // Get head arguments
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(hp, args) if *hp == predicate => args.as_slice(),
            _ => return None, // Head must be our predicate
        };

        // Build candidate_on_body = candidate applied to body (pre-state satisfies candidate)
        let candidate_on_body = self.apply_to_args(predicate, candidate, body_args)?;

        // Build violated_on_head = not(candidate) applied to head (post-state violates candidate)
        let violated = ChcExpr::not(candidate.clone());
        let violated_on_head = self.apply_to_args(predicate, &violated, head_args)?;

        // Get clause constraint (interpreted part)
        let clause_constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));

        // Build Phase 0 query: candidate_on_body ∧ clause_constraint ∧ violated_on_head
        // Note: We deliberately omit constraints from other body predicates (B1, B2, ...)
        let query = self.bound_int_vars(ChcExpr::and_all(vec![
            candidate_on_body.clone(),
            clause_constraint.clone(),
            violated_on_head.clone(),
        ]));

        // Check if we dropped any constraints (i.e., there are other body predicates)
        let missing_product_state = clause.body.predicates.len() > 1
            && clause
                .body
                .predicates
                .iter()
                .any(|(bp, _)| *bp != predicate);

        Some(HyperedgeInductiveQuery {
            query,
            candidate_on_body,
            clause_constraint,
            violated_on_head,
            missing_product_state,
        })
    }

    /// Extract concrete state equalities from a model for predicate args.
    ///
    /// #2492: Handles expression args by substituting model values and
    /// simplifying, rather than only matching direct Var args.
    fn extract_concrete_state(
        args: &[ChcExpr],
        canonical_vars: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<ChcExpr> {
        let mut concrete_parts: Vec<ChcExpr> = Vec::new();
        for (i, arg) in args.iter().enumerate() {
            let Some(canonical_var) = canonical_vars.get(i) else {
                continue;
            };
            // #6047: For array canonical vars, extract select-based constraints
            // from the model instead of trying scalar equality (which fails for arrays).
            if matches!(canonical_var.sort, ChcSort::Array(_, _)) {
                if let ChcExpr::Var(v) = arg {
                    if let Some(select_conjuncts) =
                        Self::array_select_constraints_from_model(canonical_var, model.get(&v.name))
                    {
                        concrete_parts.extend(select_conjuncts);
                    }
                }
                continue;
            }
            let canonical_expr = ChcExpr::Var(canonical_var.clone());
            match arg {
                ChcExpr::Var(v) => {
                    if let Some(val_expr) = model.get(&v.name).and_then(Self::smt_value_to_expr) {
                        concrete_parts.push(ChcExpr::eq(canonical_expr, val_expr));
                    }
                }
                expr => {
                    // Substitute all constituent vars with model values, then
                    // simplify to reduce to a constant if possible.
                    let subst: Vec<(ChcVar, ChcExpr)> = expr
                        .vars()
                        .into_iter()
                        .filter_map(|v| {
                            model
                                .get(&v.name)
                                .and_then(Self::smt_value_to_expr)
                                .map(|val| (v, val))
                        })
                        .collect();
                    if !subst.is_empty() {
                        let evaluated = expr.substitute(&subst).simplify_constants();
                        concrete_parts.push(ChcExpr::eq(canonical_expr, evaluated));
                    }
                }
            }
        }
        concrete_parts
    }

    fn smt_value_to_expr(val: &SmtValue) -> Option<ChcExpr> {
        Some(match val {
            SmtValue::Bool(b) => ChcExpr::Bool(*b),
            SmtValue::Int(n) => ChcExpr::Int(*n),
            // Beyond-i128 witness: exact Horner encoding (never wraps).
            SmtValue::BigInt(b) => ChcExpr::from_bigint(b.as_ref().clone()),
            SmtValue::Real(r) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64().unwrap_or(0);
                let d = r.denom().to_i64().unwrap_or(1);
                ChcExpr::Real(n, d)
            }
            // #5523: Preserve bitvector sort to avoid BV→Int sort mismatches.
            SmtValue::BitVec(v, w) => ChcExpr::BitVec(*v, *w),
            // #7016: DT constructor applications for counterexample concretization.
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_expr(f).map(Arc::new))
                    .collect::<Option<Vec<_>>>()?;
                ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                )
            }
            SmtValue::Opaque(name) => {
                ChcExpr::FuncApp(name.clone(), ChcSort::Uninterpreted(name.clone()), vec![])
            }
            // Array values have no scalar ChcExpr representation here.
            SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. } => {
                return None;
            }
        })
    }
}
