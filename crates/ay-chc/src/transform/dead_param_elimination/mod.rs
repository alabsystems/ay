// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Dead parameter elimination for CHC problems.
//!
//! Removes predicate parameters that are never referenced in constraints
//! or used at live positions in other predicate applications. This reduces
//! the state space for PDR and other engines, enabling them to synthesize
//! invariants over fewer variables.
//!
//! # Algorithm (based on Z3's `dl_mk_slice`)
//!
//! 1. Initialize all parameter positions as "potentially dead".
//! 2. Mark a position as *live* if:
//!    a. The corresponding argument in any clause is a constant (not a variable).
//!    b. The corresponding argument variable appears in the clause's constraint.
//!    c. The corresponding argument variable appears in another predicate
//!    application at a position that is already live (liveness propagation).
//!    d. The corresponding argument variable appears in multiple **body**
//!    predicate applications (cross-predicate join dependency).
//!    Note: a variable appearing once in the body and once in the head
//!    at the same position is a frame condition (passthrough) and is NOT
//!    a cross-predicate dependency. Only body-to-body sharing triggers this.
//! 3. Iterate to fixpoint (since liveness propagates through predicate calls).
//! 4. Remove dead positions from predicate declarations and rewrite clauses.
//!
//! # Back-translation
//!
//! When translating invariants back, dead parameters are re-inserted as
//! unconstrained (the invariant formula doesn't mention them, which is correct
//! since they were irrelevant to the proof).
//!
//! Reference: `reference/z3/src/muz/transforms/dl_mk_slice.cpp`
//! Part of #5826

mod analysis;

use crate::{
    ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    BackTranslator, InvalidityWitness, TransformMemoryReport, TransformationResult, Transformer,
    ValidityWitness,
};

/// Dead parameter elimination transformer.
///
/// Analyzes which predicate argument positions are "dead" (never contribute
/// to the satisfiability/unsatisfiability of the CHC system) and removes them.
pub(crate) struct DeadParamEliminator {
    verbose: bool,
}

impl Default for DeadParamEliminator {
    fn default() -> Self {
        Self::new()
    }
}

impl DeadParamEliminator {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Analyze and eliminate dead parameters, returning the transformed problem
    /// and a mapping from (predicate_id, old_position) -> new_position (or None if dead).
    pub(crate) fn eliminate(
        &self,
        problem: &ChcProblem,
    ) -> (ChcProblem, FxHashMap<PredicateId, Vec<Option<usize>>>) {
        let live = self.compute_live_positions(problem);

        // Build position mapping: for each predicate, old_pos -> new_pos (or None)
        let mut position_map: FxHashMap<PredicateId, Vec<Option<usize>>> = FxHashMap::default();
        let mut total_eliminated = 0;

        for pred in problem.predicates() {
            let live_set = live.get(&pred.id);
            let mut mapping = Vec::with_capacity(pred.arity());
            let mut new_idx = 0;
            for old_idx in 0..pred.arity() {
                if live_set.map_or(false, |s| s.contains(&old_idx)) {
                    mapping.push(Some(new_idx));
                    new_idx += 1;
                } else {
                    mapping.push(None);
                    total_eliminated += 1;
                }
            }
            position_map.insert(pred.id, mapping);
        }

        if total_eliminated == 0 {
            return (problem.clone(), position_map);
        }

        if self.verbose {
            for pred in problem.predicates() {
                let mapping = &position_map[&pred.id];
                let dead: Vec<usize> = mapping
                    .iter()
                    .enumerate()
                    .filter_map(|(i, m)| if m.is_none() { Some(i) } else { None })
                    .collect();
                if !dead.is_empty() {
                    tracing::info!(
                        action = "DeadParamElim",
                        predicate = %pred.name,
                        dead_positions = ?dead,
                        old_arity = pred.arity(),
                        new_arity = pred.arity() - dead.len(),
                        "CHC: dead-param-elim: {} — removing positions {:?} (arity {} -> {})",
                        pred.name, dead, pred.arity(), pred.arity() - dead.len(),
                    );
                }
            }
        }

        // Build new problem with reduced predicates
        let mut new_problem = ChcProblem::new();
        // Preserve datatype definitions (problem-level routing metadata,
        // #7016): parameter elimination never touches datatype declarations,
        // and dropping them silently degraded downstream executor routing on
        // DT problems (#chc25-dtbv-lane-perf).
        for (name, ctors) in problem.datatype_defs() {
            new_problem.add_datatype_def(name.clone(), ctors.clone());
        }

        // Declare predicates with reduced arities
        for pred in problem.predicates() {
            let mapping = &position_map[&pred.id];
            let new_sorts: Vec<ChcSort> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .filter_map(|(i, sort)| {
                    if mapping[i].is_some() {
                        Some(sort.clone())
                    } else {
                        None
                    }
                })
                .collect();
            new_problem.declare_predicate(&pred.name, new_sorts);
        }

        // Rewrite clauses
        for clause in problem.clauses() {
            let new_clause = self.rewrite_clause(clause, &position_map);
            new_problem.add_clause(new_clause);
        }

        if problem.is_fixedpoint_format() {
            new_problem.set_fixedpoint_format();
        }

        if self.verbose {
            tracing::info!(
                action = "DeadParamElimSummary",
                total_eliminated = total_eliminated,
                "CHC: dead-param-elim: removed {total_eliminated} parameters total",
            );
        }

        (new_problem, position_map)
    }
    /// Rewrite a clause by removing dead argument positions from predicate applications.
    fn rewrite_clause(
        &self,
        clause: &HornClause,
        position_map: &FxHashMap<PredicateId, Vec<Option<usize>>>,
    ) -> HornClause {
        let new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let mapping = &position_map[pred_id];
                let new_args: Vec<ChcExpr> = args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, arg)| {
                        if i < mapping.len() && mapping[i].is_some() {
                            Some(arg.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                (*pred_id, new_args)
            })
            .collect();

        let new_body = ClauseBody::new(new_body_preds, clause.body.constraint.clone());

        let new_head = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => {
                let mapping = &position_map[pred_id];
                let new_args: Vec<ChcExpr> = args
                    .iter()
                    .enumerate()
                    .filter_map(|(i, arg)| {
                        if i < mapping.len() && mapping[i].is_some() {
                            Some(arg.clone())
                        } else {
                            None
                        }
                    })
                    .collect();
                ClauseHead::Predicate(*pred_id, new_args)
            }
            ClauseHead::False => ClauseHead::False,
        };

        HornClause::new(new_body, new_head)
    }
}

impl Transformer for DeadParamEliminator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let (new_problem, position_map) = self.eliminate(&problem);

        // Check if any parameters were actually eliminated
        let any_eliminated = position_map
            .values()
            .any(|mapping| mapping.iter().any(Option::is_none));

        if !any_eliminated {
            return TransformationResult {
                problem: new_problem,
                back_translator: Box::new(super::IdentityBackTranslator),
            };
        }

        // Build back-translator that re-inserts dead parameters
        let mut original_sorts: FxHashMap<PredicateId, Vec<ChcSort>> = FxHashMap::default();
        for pred in problem.predicates() {
            original_sorts.insert(pred.id, pred.arg_sorts.clone());
        }

        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(DeadParamBackTranslator {
                position_map,
                original_sorts,
                input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                    .then(|| std::sync::Arc::new(problem)),
            }),
        }
    }
}

/// Back-translator that re-inserts dead parameters into invariant models.
///
/// Dead parameters are re-inserted as unconstrained variables in the
/// predicate interpretation. The invariant formula doesn't mention them,
/// which is correct since they were irrelevant to the proof.
struct DeadParamBackTranslator {
    /// For each predicate: old_position -> new_position (or None if dead)
    position_map: FxHashMap<PredicateId, Vec<Option<usize>>>,
    /// Original argument sorts for each predicate (before elimination)
    original_sorts: FxHashMap<PredicateId, Vec<ChcSort>>,
    /// INPUT problem, retained for ground back-translation only.
    ///
    /// Slicing keeps every clause and its order, so the ground derivation maps
    /// across index-for-index; the dropped argument positions reappear as
    /// unconstrained clause variables and are filled by ground completion
    /// (they are dead by construction, so any value that survives validation is
    /// as good as the original one).
    input_problem: Option<std::sync::Arc<crate::ChcProblem>>,
}

impl BackTranslator for DeadParamBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let input_problem = self.input_problem.clone()?;
        let candidates = (0..input_problem.clauses().len())
            .map(|index| vec![index])
            .collect();
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::new(
            "dead-param-eliminator",
            input_problem,
            candidates,
        )
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "dead-param-eliminator"
    }

    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        use crate::pdr::PredicateInterpretation;

        let mut new_interpretations = FxHashMap::default();

        for (pred_id, interp) in witness.iter() {
            let mapping = match self.position_map.get(pred_id) {
                Some(m) => m,
                None => {
                    new_interpretations.insert(*pred_id, interp.clone());
                    continue;
                }
            };

            let original_sorts = match self.original_sorts.get(pred_id) {
                Some(s) => s,
                None => {
                    new_interpretations.insert(*pred_id, interp.clone());
                    continue;
                }
            };

            // Rebuild the variable list with dead parameters re-inserted
            let mut new_vars = Vec::with_capacity(original_sorts.len());
            let mut reduced_idx = 0;
            for (old_idx, sort) in original_sorts.iter().enumerate() {
                if old_idx < mapping.len() && mapping[old_idx].is_some() {
                    // Live parameter — use the variable from the reduced interpretation
                    if reduced_idx < interp.vars.len() {
                        new_vars.push(interp.vars[reduced_idx].clone());
                    } else {
                        // Fallback: create a fresh variable
                        new_vars.push(ChcVar::new(
                            format!("__dead_{pred_id}_{old_idx}"),
                            sort.clone(),
                        ));
                    }
                    reduced_idx += 1;
                } else {
                    // Dead parameter — insert a fresh unconstrained variable
                    new_vars.push(ChcVar::new(
                        format!("__dead_{pred_id}_{old_idx}"),
                        sort.clone(),
                    ));
                }
            }

            new_interpretations.insert(
                *pred_id,
                PredicateInterpretation::new(new_vars, interp.formula.clone()),
            );
        }

        let mut new_witness = crate::InvariantModel::new();
        for (pred_id, interp) in new_interpretations {
            new_witness.set(pred_id, interp);
        }
        new_witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        // Counterexample steps don't reference predicate parameters directly,
        // so no translation is needed.
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::reversible("dead_param_elimination")
    }
}

#[cfg(test)]
mod tests;
