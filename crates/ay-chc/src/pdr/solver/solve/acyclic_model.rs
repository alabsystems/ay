// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The invariant model `try_acyclic_safety_proof` hands to `verify_model`.
//!
//! Once every query of a transition-free problem is proven unreachable, the
//! natural model interprets each predicate as the disjunction of its facts'
//! canonical constraints. A fact whose constraint mentions variables that are
//! not head arguments (fact-LOCAL variables) leaves those variables free in
//! that disjunct, and `verify_model` rejects any interpretation with a free
//! variable as capture-unsound (the 022c-horn_000 guard). Every such model was
//! therefore refused after the queries had already been decided, and the solve
//! fell through to the full PDR search.
//!
//! That fall-through is not only slower. The model-checker-consumer termination VC of a
//! `while i < n invariant .. decreases n - i` loop over `u64` is exactly this
//! shape: a single NULLARY `error` predicate whose one fact carries the whole
//! verification condition, so every variable is fact-local. The acyclic check
//! decides it with one SMT query, while the full search runs startup discovery
//! and model cascades under fixed wall-clock budgets that CPU contention
//! exhausts; under parallel load the search then either runs to the caller's
//! deadline or yields a candidate the proof boundary refuses. Measured
//! 2026-09-28 through `solve_pdr_proof` with a 120s budget: about 0.35s
//! serially, but with the CPU oversubscribed ~9x in-process, 12 of 12 solves
//! in one run and 8 of 12 in another ran to the 120s deadline as Unknown.
//!
//! The disjunct is closed here instead, exactly and without quantifier
//! elimination, in the two cases where `exists locals. constraint` has a
//! closed, local-free equivalent:
//!
//! * the fact constraint is unsatisfiable on its own: the fact clause is
//!   vacuous and the disjunct is `false`, for a predicate of any arity;
//! * the predicate is nullary and the fact constraint is satisfiable: the
//!   disjunct `exists locals. constraint` is the closed formula `true`.
//!
//! Anything else (a satisfiable fact with locals on a predicate with
//! arguments, or an inconclusive check) bails exactly as before. The free
//! variable guard is untouched, and soundness never rests on this
//! construction: the caller still runs the complete `verify_model` clause
//! check on whatever model is built here.

use super::{
    ChcExpr, FxHashMap, InvariantModel, PdrSolver, PredicateId, PredicateInterpretation, SmtResult,
};
use ay_core::kani_compat::DetHashSet as FxHashSet;

impl PdrSolver {
    /// Build the acyclic-safety model from each predicate's fact disjuncts,
    /// closing every disjunct over fact-local variables (see the module docs).
    ///
    /// `fact_disjuncts` maps a predicate to `(fact clause index, canonical
    /// constraint)` pairs. `facts_unsat_alone` holds the clause indices of facts
    /// whose constraint the query checks already proved unsatisfiable on its
    /// own, so no query is repeated for them.
    ///
    /// Returns `None` when a disjunct cannot be closed exactly or the solve was
    /// cancelled; the caller then bails, as it always did for such a model.
    pub(super) fn build_acyclic_safety_model(
        &mut self,
        fact_disjuncts: &FxHashMap<PredicateId, Vec<(usize, ChcExpr)>>,
        facts_unsat_alone: &FxHashSet<usize>,
    ) -> Option<InvariantModel> {
        let mut model = InvariantModel::new();
        let predicate_ids: Vec<PredicateId> = self
            .problem
            .predicates()
            .iter()
            .map(|pred| pred.id)
            .collect();
        for pred_id in predicate_ids {
            let vars = self
                .caches
                .predicate_vars
                .get(&pred_id)
                .cloned()
                .unwrap_or_default();
            let mut disjuncts = Vec::new();
            let mut closed_true = false;
            for (fact_index, disjunct) in fact_disjuncts.get(&pred_id).into_iter().flatten() {
                let has_local = disjunct
                    .vars()
                    .iter()
                    .any(|var| !vars.iter().any(|binder| binder.name == var.name));
                if !has_local {
                    disjuncts.push(disjunct.clone());
                    continue;
                }
                if facts_unsat_alone.contains(fact_index)
                    || self.fact_constraint_is_unsat(disjunct)?
                {
                    // Vacuous fact clause: its disjunct is `false`.
                    continue;
                }
                if !vars.is_empty() {
                    // `exists locals. constraint` over head arguments would need
                    // quantifier elimination; keep the historical bail.
                    return None;
                }
                // Nullary predicate, satisfiable fact: the closed disjunct is `true`.
                closed_true = true;
            }
            let formula = if closed_true {
                ChcExpr::Bool(true)
            } else {
                match disjuncts.len() {
                    0 => ChcExpr::Bool(false),
                    1 => disjuncts.swap_remove(0),
                    _ => ChcExpr::or_all(disjuncts),
                }
            };
            model.set(pred_id, PredicateInterpretation::new(vars, formula));
        }
        Some(model)
    }

    /// Decide one fact constraint on its own: `Some(true)` when unsatisfiable,
    /// `Some(false)` when satisfiable, `None` when cancelled or inconclusive.
    fn fact_constraint_is_unsat(&mut self, constraint: &ChcExpr) -> Option<bool> {
        if self.is_cancelled() {
            return None;
        }
        let bounded = self.bound_int_vars(constraint.clone());
        match self.check_sat_via_executor_backend(&bounded) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                Some(true)
            }
            SmtResult::Sat(_) => Some(false),
            SmtResult::Unknown => None,
        }
    }
}

#[cfg(test)]
#[path = "acyclic_model_tests.rs"]
mod tests;
