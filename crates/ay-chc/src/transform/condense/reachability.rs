// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Unreachable-clause elimination for the condense superpass.
//!
//! Mirrors Eldarica's `ReachabilityChecker` (fwd) and Golem's
//! `RemoveUnreachableNodes` (fwd+bwd) as *ideas* (no code copied):
//!
//! - **Forward-unreachable** predicates (no hyper-resolution derivation from
//!   fact clauses can ever produce a fact for them) are interpreted as `false`
//!   in back-translated models; every clause mentioning one in its body can
//!   never fire and is removed.
//! - **Backward-irrelevant** predicates (no path in the clause dependency
//!   graph from them to any query clause) are interpreted as `true`; every
//!   clause whose head is backward-irrelevant is removed.
//!
//! Both sets are computed purely syntactically over the clause graph, which
//! over-approximates real reachability — removal is therefore sound in both
//! directions:
//!
//! - UNSAT is preserved exactly: any derivation of `false` uses only clauses
//!   whose body predicates are forward-reachable and whose heads reach the
//!   query, i.e. only kept clauses. Counterexample clause indices are remapped
//!   to the original indices (fail-closed replay validates them).
//! - SAT is preserved exactly: a model of the kept clauses extends to the
//!   original problem by interpreting forward-unreachable predicates as
//!   `false` and remaining absent (backward-irrelevant) predicates as `true`.
//!   Predicates in these sets never occur in kept clauses, so the extension
//!   cannot invalidate the kept-clause model, and each removed clause is
//!   satisfied by construction (a `false` body conjunct or a `true` head).

use crate::{ChcExpr, ChcProblem, ChcVar, HornClause, PredicateId, PredicateInterpretation};
use ay_core::kani_compat::DetHashSet as FxHashSet;

use super::super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};
use super::ClauseIndexMap;

/// Remove clauses that cannot participate in any derivation of `false`.
pub(crate) struct UnreachableClauseEliminator {
    verbose: bool,
}

impl UnreachableClauseEliminator {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Predicates derivable from fact clauses (syntactic over-approximation).
    fn forward_reachable(clauses: &[HornClause]) -> FxHashSet<PredicateId> {
        let mut reachable: FxHashSet<PredicateId> = FxHashSet::default();
        loop {
            let mut changed = false;
            for clause in clauses {
                let Some(head) = clause.head.predicate_id() else {
                    continue;
                };
                if reachable.contains(&head) {
                    continue;
                }
                if clause
                    .body
                    .predicates
                    .iter()
                    .all(|(pid, _)| reachable.contains(pid))
                {
                    reachable.insert(head);
                    changed = true;
                }
            }
            if !changed {
                return reachable;
            }
        }
    }

    /// Predicates from which a query clause is reachable in the clause graph.
    fn backward_relevant(clauses: &[HornClause]) -> FxHashSet<PredicateId> {
        let mut relevant: FxHashSet<PredicateId> = FxHashSet::default();
        loop {
            let mut changed = false;
            for clause in clauses {
                let head_relevant = match clause.head.predicate_id() {
                    None => true, // query clause: body predicates feed `false`
                    Some(head) => relevant.contains(&head),
                };
                if !head_relevant {
                    continue;
                }
                for (pid, _) in &clause.body.predicates {
                    if relevant.insert(*pid) {
                        changed = true;
                    }
                }
            }
            if !changed {
                return relevant;
            }
        }
    }
}

impl Transformer for UnreachableClauseEliminator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let clauses = problem.clauses();
        let forward = Self::forward_reachable(clauses);
        let backward = Self::backward_relevant(clauses);

        let keep = |clause: &HornClause| -> bool {
            let body_derivable = clause
                .body
                .predicates
                .iter()
                .all(|(pid, _)| forward.contains(pid));
            let head_relevant = clause
                .head
                .predicate_id()
                .map_or(true, |head| backward.contains(&head));
            body_derivable && head_relevant
        };

        if clauses.iter().all(keep) {
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }

        // Rebuild with identical predicate declarations (ids stay stable);
        // dropped predicates become harmless orphans that the ClauseInliner
        // compaction removes later in the condense round.
        let mut new_problem = ChcProblem::new();
        for pred in problem.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        let mut index_map = ClauseIndexMap::new();
        for (idx, clause) in clauses.iter().enumerate() {
            if keep(clause) {
                index_map.record_add(&mut new_problem, clause.clone(), idx);
            }
        }
        if problem.is_fixedpoint_format() {
            new_problem.set_fixedpoint_format();
        }
        for (name, ctors) in problem.datatype_defs() {
            new_problem.add_datatype_def(name.clone(), ctors.clone());
        }
        for name in problem.action_names() {
            new_problem.declare_action(name.clone());
        }
        if problem.has_query_evidence() && !new_problem.has_query_evidence() {
            new_problem.add_clause(HornClause::new(
                crate::ClauseBody::new(Vec::new(), Some(ChcExpr::Bool(false))),
                crate::ClauseHead::False,
            ));
        }

        // Predicates absent from every kept clause get a fixed interpretation
        // on back-translation: `false` if forward-unreachable, else `true`
        // (backward-irrelevant).
        let mut absent: FxHashSet<PredicateId> =
            problem.predicates().iter().map(|p| p.id).collect();
        for clause in new_problem.clauses() {
            for (pid, _) in &clause.body.predicates {
                absent.remove(pid);
            }
            if let Some(pid) = clause.head.predicate_id() {
                absent.remove(&pid);
            }
        }
        let mut fixed_interps: Vec<(PredicateId, Vec<ChcVar>, bool)> = Vec::new();
        for pred in problem.predicates() {
            if !absent.contains(&pred.id) {
                continue;
            }
            let vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("__unreach_{}_{i}", pred.id.0), sort.clone()))
                .collect();
            let value = forward.contains(&pred.id);
            fixed_interps.push((pred.id, vars, value));
        }

        if self.verbose {
            safe_eprintln!(
                "CHC condense reachability: {} -> {} clauses ({} predicates fixed)",
                clauses.len(),
                new_problem.clauses().len(),
                fixed_interps.len()
            );
        }

        TransformationResult {
            problem: new_problem,
            back_translator: Box::new(UnreachableBackTranslator {
                fixed_interps,
                index_map,
                input_problem: crate::ground_derivation::ground_backtranslation_enabled()
                    .then(|| std::sync::Arc::new(problem)),
            }),
        }
    }
}

/// Back-translator for [`UnreachableClauseEliminator`].
struct UnreachableBackTranslator {
    /// Predicates absent from the reduced problem: `(id, vars, value)` where
    /// `value == false` marks forward-unreachable predicates and `true` marks
    /// backward-irrelevant ones.
    fixed_interps: Vec<(PredicateId, Vec<ChcVar>, bool)>,
    /// Kept-clause index -> original clause index.
    index_map: ClauseIndexMap,
    /// INPUT problem, retained for ground back-translation only.
    input_problem: Option<std::sync::Arc<ChcProblem>>,
}

impl BackTranslator for UnreachableBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        self.index_map
            .ground_translator("unreachable-clause-eliminator", self.input_problem.clone()?)
            .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "unreachable-clause-eliminator"
    }

    fn translate_validity(&self, mut witness: ValidityWitness) -> ValidityWitness {
        for (pred_id, vars, value) in &self.fixed_interps {
            // Overwrite unconditionally: the predicate occurs in NO kept
            // clause, so the reduced-problem solver may have emitted an
            // arbitrary (typically `false`) orphan interpretation. Only the
            // computed polarity satisfies the removed original clauses.
            witness.set(
                *pred_id,
                PredicateInterpretation::new(vars.clone(), ChcExpr::Bool(*value)),
            );
        }
        witness
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        self.index_map.translate_invalidity(witness)
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "unreachable_clause_elimination",
            [
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
    }
}
