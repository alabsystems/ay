// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Helper methods for safety-proof checks.
//!
//! Contains:
//! - `algebraic_model_blocks_all_errors`: check if algebraic-only model blocks errors
//! - `extract_conjuncts`: leaf-level AND-tree conjunct extraction
//! - `negate_atomic_constraint`: negate a comparison to produce candidate lemma
//! - `check_backward_chain_safety`: backward-chain safety for predicates without invariants

use super::*;

impl PdrSolver {
    /// Check if a model built from ONLY algebraically-verified lemmas blocks
    /// all error queries. Used as a fast path in check_invariants_prove_safety
    /// to avoid the expensive verify_model cascade (#5401).
    pub(super) fn algebraic_model_blocks_all_errors(
        &mut self,
        model: &InvariantModel,
        queries: &[HornClause],
    ) -> bool {
        for query in queries {
            if query.body.predicates.len() != 1 {
                return false;
            }
            let (pred_id, body_args) = &query.body.predicates[0];
            let pred = *pred_id;

            let canonical_vars = match self.canonical_vars(pred) {
                Some(v) => v.to_vec(),
                None => return false,
            };

            let mut var_map: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (idx, canon_var) in canonical_vars.iter().enumerate() {
                if idx < body_args.len() {
                    var_map.push((canon_var.clone(), body_args[idx].clone()));
                }
            }

            let error_constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));

            let interp = match model.get(&pred) {
                Some(i) => i,
                None => return false,
            };

            if matches!(&interp.formula, ChcExpr::Bool(true)) {
                return false;
            }

            let interp_on_args = interp.formula.clone().substitute(&var_map);
            let combined = ChcExpr::and(interp_on_args.clone(), error_constraint.clone());
            self.smt.reset();
            let result = self
                .smt
                .check_sat_with_timeout(&combined, std::time::Duration::from_millis(500));
            match result {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => {
                    // (#8782): When SMT returns Unknown/Sat on mod-heavy formulas,
                    // try syntactic contradiction via mod-substitution. Build synthetic
                    // lemmas from the model's conjuncts and apply the same mod-substitution
                    // + syntactic contradiction checks used by the main safety proof.
                    let synthetic_lemmas: Vec<Lemma> = interp_on_args
                        .collect_conjuncts()
                        .into_iter()
                        .map(|c| Lemma::new(pred, c, 1))
                        .collect();
                    let syntactic_ok = Self::error_contradicts_invariants(
                        &error_constraint,
                        &synthetic_lemmas,
                        pred,
                    );
                    if syntactic_ok {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: algebraic_model_blocks_all_errors: pred {} error blocked by syntactic contradiction",
                                pred.index(),
                            );
                        }
                    } else if let Some(simplified) =
                        Self::apply_mod_substitution(&error_constraint, &synthetic_lemmas, pred)
                    {
                        let syntactic_after_mod = Self::error_contradicts_invariants(
                            &simplified,
                            &synthetic_lemmas,
                            pred,
                        );
                        if syntactic_after_mod {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: algebraic_model_blocks_all_errors: pred {} error blocked by mod-substitution + syntactic contradiction",
                                    pred.index(),
                                );
                            }
                        } else {
                            // Try SMT on simplified formula
                            let simp_combined = ChcExpr::and(interp_on_args, simplified);
                            self.smt.reset();
                            match self.smt.check_sat_with_timeout(
                                &simp_combined,
                                std::time::Duration::from_millis(500),
                            ) {
                                SmtResult::Unsat
                                | SmtResult::UnsatWithCore(_)
                                | SmtResult::UnsatWithFarkas(_) => {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: algebraic_model_blocks_all_errors: pred {} error blocked by mod-substitution + SMT",
                                            pred.index(),
                                        );
                                    }
                                }
                                _ => return false,
                            }
                        }
                    } else {
                        return false;
                    }
                }
            }
        }
        true
    }

    /// Extract atomic conjuncts from an expression.
    /// Returns the leaf-level conjuncts of an AND tree.
    pub(super) fn extract_conjuncts(expr: &ChcExpr) -> Vec<ChcExpr> {
        expr.conjuncts().into_iter().cloned().collect()
    }

    /// Negate an atomic comparison constraint to produce a candidate lemma.
    ///
    /// - `NOT(a <= b)` (i.e., `a > b`) → lemma `a <= b`  (equivalently `b >= a`)
    /// - `a <= b` → lemma `NOT(a <= b)`, i.e., `a > b` → `a >= b + 1`
    /// - `NOT(a >= b)` (i.e., `a < b`) → lemma `a >= b`
    /// - `a >= b` → lemma `a < b` → `b >= a + 1`
    ///
    /// Returns None for non-comparison expressions.
    pub(super) fn negate_atomic_constraint(expr: &ChcExpr) -> Option<ChcExpr> {
        match expr {
            // NOT(a <= b) means a > b. Lemma: a <= b, i.e., b >= a.
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                match args[0].as_ref() {
                    ChcExpr::Op(ChcOp::Le, inner) if inner.len() == 2 => {
                        // NOT(a <= b) → lemma: a <= b
                        Some(ChcExpr::le(
                            inner[0].as_ref().clone(),
                            inner[1].as_ref().clone(),
                        ))
                    }
                    ChcExpr::Op(ChcOp::Ge, inner) if inner.len() == 2 => {
                        // NOT(a >= b) → lemma: a >= b
                        Some(ChcExpr::ge(
                            inner[0].as_ref().clone(),
                            inner[1].as_ref().clone(),
                        ))
                    }
                    ChcExpr::Op(ChcOp::Lt, inner) if inner.len() == 2 => {
                        // NOT(a < b) → lemma: a >= b
                        Some(ChcExpr::ge(
                            inner[0].as_ref().clone(),
                            inner[1].as_ref().clone(),
                        ))
                    }
                    ChcExpr::Op(ChcOp::Gt, inner) if inner.len() == 2 => {
                        // NOT(a > b) → lemma: a <= b
                        Some(ChcExpr::le(
                            inner[0].as_ref().clone(),
                            inner[1].as_ref().clone(),
                        ))
                    }
                    ChcExpr::Op(ChcOp::Eq, _inner) if _inner.len() == 2 => {
                        // NOT(a = b): can't negate to a simple lemma
                        None
                    }
                    _ => None,
                }
            }
            // a <= b → lemma: NOT(a <= b), i.e., a > b → a >= b+1
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                // a <= b negated is a >= b+1
                Some(ChcExpr::ge(
                    args[0].as_ref().clone(),
                    ChcExpr::add(args[1].as_ref().clone(), ChcExpr::Int(1.into())),
                ))
            }
            // a >= b → lemma: NOT(a >= b), i.e., a < b → b >= a+1
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => Some(ChcExpr::ge(
                args[1].as_ref().clone(),
                ChcExpr::add(args[0].as_ref().clone(), ChcExpr::Int(1.into())),
            )),
            // a < b → lemma: a >= b
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => Some(ChcExpr::ge(
                args[0].as_ref().clone(),
                args[1].as_ref().clone(),
            )),
            // a > b → lemma: a <= b, i.e., b >= a
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => Some(ChcExpr::ge(
                args[1].as_ref().clone(),
                args[0].as_ref().clone(),
            )),
            _ => None,
        }
    }

    /// Backward-chain safety check: when a query predicate has no frame[1]
    /// invariants, check if predecessor predicates' invariants make the error
    /// unreachable through all defining clauses.
    ///
    /// For each clause `P(body_args) ∧ constraint → Q(head_args)` that defines
    /// the query predicate Q, check:
    ///   P_invariants(body_args) ∧ constraint ∧ error_constraint(head_args) is UNSAT
    ///
    /// If ALL defining clauses produce UNSAT, the error is unreachable.
    /// #1306: enables dillig12_m where FUN invariant D=2*C makes the FUN→SAD
    /// transition produce only safe SAD states.
    pub(super) fn check_backward_chain_safety(
        &mut self,
        query_pred: PredicateId,
        error_constraint: &ChcExpr,
        query_canonical_vars: &[ChcVar],
    ) -> bool {
        let clauses: Vec<_> = self.problem.clauses_defining(query_pred).cloned().collect();
        if clauses.is_empty() {
            return false;
        }

        let mut checked_any = false;
        for clause in &clauses {
            if clause.body.predicates.is_empty() {
                // Fact clause for query pred: check error against init constraint
                let constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));
                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };
                // Map head args to canonical vars for error_constraint
                let mut canon_to_head: FxHashMap<String, ChcExpr> = FxHashMap::default();
                for (head_arg, canon) in head_args.iter().zip(query_canonical_vars.iter()) {
                    canon_to_head.insert(canon.name.clone(), head_arg.clone());
                }
                let error_on_head = error_constraint.substitute_name_map(&canon_to_head);
                let query = ChcExpr::and(constraint, error_on_head);
                self.smt.reset();
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        checked_any = true;
                        continue;
                    }
                    _ => return false,
                }
            }

            if clause.body.predicates.len() != 1 {
                return false; // Conservative for multi-body
            }

            let (source_pred, body_args) = &clause.body.predicates[0];
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            // Self-loop of query pred: skip (would need own invariants)
            if *source_pred == query_pred {
                continue;
            }

            // Get source predicate's invariants
            let source_canonical = match self.canonical_vars(*source_pred) {
                Some(v) => v.to_vec(),
                None => return false,
            };
            let mut source_invariants: Vec<ChcExpr> = Vec::new();
            for lemma in &self.frames[1].lemmas {
                if lemma.predicate == *source_pred {
                    source_invariants.push(lemma.formula.clone());
                }
            }
            if source_invariants.is_empty() {
                return false; // Source also has no invariants
            }

            // Apply source invariants to body args
            let mut canon_to_body: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for (body_arg, canon) in body_args.iter().zip(source_canonical.iter()) {
                canon_to_body.insert(canon.name.clone(), body_arg.clone());
            }
            let inv_on_body = source_invariants
                .iter()
                .map(|inv| inv.substitute_name_map(&canon_to_body))
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));

            // Apply error constraint to head args
            let mut canon_to_head: FxHashMap<String, ChcExpr> = FxHashMap::default();
            for (head_arg, canon) in head_args.iter().zip(query_canonical_vars.iter()) {
                canon_to_head.insert(canon.name.clone(), head_arg.clone());
            }
            let error_on_head = error_constraint.substitute_name_map(&canon_to_head);

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Full check: source_invariants(body) ∧ clause_constraint ∧ error(head) is SAT?
            let query = ChcExpr::and_all(vec![inv_on_body, clause_constraint, error_on_head]);
            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    checked_any = true;
                    continue;
                }
                _ => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: backward-chain: clause from pred {} to pred {} is SAT (error reachable)",
                            source_pred.index(),
                            query_pred.index()
                        );
                    }
                    return false;
                }
            }
        }
        checked_any
    }
}
