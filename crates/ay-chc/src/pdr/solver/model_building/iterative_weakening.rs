// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Iterative weakening of model conjuncts.
//!
//! Removes non-inductive conjuncts in rounds until a fixpoint, then
//! verifies the weakened model. Also contains conjunct-level helpers.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcVar, PredicateId};
use crate::{InvariantModel, PredicateInterpretation};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Build a model by removing non-inductive conjuncts in bulk.
    ///
    /// For each predicate, checks each conjunct against ALL transition clauses
    /// where that predicate appears as the head. A conjunct is kept only if
    /// `body ∧ conjunct_body ⇒ conjunct_head` holds for every such clause
    /// (checked via SMT: `body ∧ conjunct_body ∧ ¬conjunct_head` is UNSAT).
    ///
    /// This handles cases where the frame contains individually self-inductive
    /// lemmas that are NOT jointly inductive across inter-predicate transitions
    /// with OR-split constraints (e.g., scaled difference bounds like
    /// `A - 3B >= -3` that aren't preserved by all branches of the OR).
    ///
    /// Part of #2834.
    pub(in crate::pdr::solver) fn build_model_with_iterative_weakening(
        &mut self,
        base_model: &InvariantModel,
    ) -> Option<InvariantModel> {
        // Decompose each predicate's formula into top-level conjuncts.
        let mut pred_conjuncts: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();
        let mut pred_vars: FxHashMap<PredicateId, Vec<ChcVar>> = FxHashMap::default();

        for (pred_id, interp) in base_model.iter() {
            pred_conjuncts.insert(*pred_id, interp.formula.collect_conjuncts());
            pred_vars.insert(*pred_id, interp.vars.clone());
        }

        let clauses: Vec<_> = self.problem.clauses().to_vec();

        // Iterate: remove non-inductive conjuncts, rebuild model, re-check.
        // Each round may expose new non-inductive conjuncts because weakening
        // the body predicate's invariant weakens the body side of implications.
        const MAX_ROUNDS: usize = 5;
        let mut total_removed = 0;

        for round in 0..MAX_ROUNDS {
            // Build current model from remaining conjuncts.
            let current_model = Self::build_model_from_conjuncts(&pred_conjuncts, &pred_vars);
            let mut removed_this_round = 0;

            // Sort predicates for deterministic weakening order (#3060)
            let mut sorted_preds: Vec<_> = pred_vars.keys().copied().collect();
            sorted_preds.sort_unstable_by_key(|pid| pid.index());
            for pred_id in sorted_preds {
                let conjuncts = match pred_conjuncts.get(&pred_id) {
                    Some(c) if c.len() > 1 => c.clone(),
                    _ => continue,
                };

                // Find all transition clauses where this predicate is the head.
                let head_clauses: Vec<_> = clauses
                    .iter()
                    .filter(|c| c.head.predicate_id() == Some(pred_id))
                    .collect();

                if head_clauses.is_empty() {
                    continue;
                }

                let vars = match pred_vars.get(&pred_id) {
                    Some(v) => v,
                    None => continue,
                };
                let mut keep = vec![true; conjuncts.len()];

                for (cidx, conjunct) in conjuncts.iter().enumerate() {
                    for clause in &head_clauses {
                        let head_args = match &clause.head {
                            crate::ClauseHead::Predicate(_, args) => args,
                            _ => continue,
                        };

                        // Build body under current model
                        let body = match self.clause_body_under_model(&clause.body, &current_model)
                        {
                            Some(b) => self.bound_int_vars(b),
                            None => continue,
                        };

                        // Apply this single conjunct to head args
                        let head_conjunct =
                            match Self::apply_single_conjunct(conjunct, vars, head_args) {
                                Some(h) => self.bound_int_vars(h),
                                None => continue,
                            };

                        // Check: body ∧ ¬conjunct_head is SAT?
                        // If SAT, the conjunct is NOT inductive on this clause.
                        let query = self.bound_int_vars(ChcExpr::and(
                            body.clone(),
                            ChcExpr::not(head_conjunct),
                        ));

                        self.smt.reset();
                        match self
                            .smt
                            .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
                        {
                            SmtResult::Unsat
                            | SmtResult::UnsatWithCore(_)
                            | SmtResult::UnsatWithFarkas(_) => {
                                // Conjunct is inductive on this clause, continue
                            }
                            _ => {
                                // Conjunct fails on this clause — remove it.
                                keep[cidx] = false;
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Iterative weakening round {}: removing conjunct from pred {}: {}",
                                        round, pred_id.index(), conjunct
                                    );
                                }
                                break; // No need to check other clauses
                            }
                        }
                    }
                }

                // Apply removals
                let new_conjuncts: Vec<ChcExpr> = conjuncts
                    .iter()
                    .enumerate()
                    .filter(|(i, _)| keep[*i])
                    .map(|(_, c)| c.clone())
                    .collect();

                let removed = conjuncts.len() - new_conjuncts.len();
                if removed > 0 {
                    removed_this_round += removed;
                    pred_conjuncts.insert(pred_id, new_conjuncts);
                }
            }

            total_removed += removed_this_round;
            if removed_this_round == 0 {
                break; // Fixpoint reached
            }
        }

        if total_removed == 0 {
            return None;
        }

        // Build the weakened model and verify it.
        let model = Self::build_model_from_conjuncts(&pred_conjuncts, &pred_vars);

        if self.verify_model(&model) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Iteratively weakened model verified (removed {} conjuncts)",
                    total_removed
                );
            }
            Some(model)
        } else {
            if self.config.verbose {
                safe_eprintln!("PDR: Iteratively weakened model still failed verification");
            }
            None
        }
    }

    /// Build an InvariantModel from per-predicate conjunct vectors.
    fn build_model_from_conjuncts(
        pred_conjuncts: &FxHashMap<PredicateId, Vec<ChcExpr>>,
        pred_vars: &FxHashMap<PredicateId, Vec<ChcVar>>,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for (pred_id, conjuncts) in pred_conjuncts {
            let formula = if conjuncts.is_empty() {
                ChcExpr::Bool(true)
            } else {
                ChcExpr::and_all(conjuncts.clone())
            };
            let vars = pred_vars.get(pred_id).cloned().unwrap_or_default();
            model.set(*pred_id, PredicateInterpretation::new(vars, formula));
        }
        model
    }

    /// Apply a single conjunct formula to head arguments.
    ///
    /// Substitutes predicate canonical variables with clause-local head arguments.
    fn apply_single_conjunct(
        conjunct: &ChcExpr,
        vars: &[ChcVar],
        head_args: &[ChcExpr],
    ) -> Option<ChcExpr> {
        if vars.len() != head_args.len() {
            return None;
        }
        let subst: Vec<(ChcVar, ChcExpr)> = vars
            .iter()
            .cloned()
            .zip(head_args.iter().cloned())
            .collect();
        Some(conjunct.substitute(&subst))
    }
}
