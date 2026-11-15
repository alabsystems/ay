// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Graph-based CHC multi-edge merger.

use crate::chc_graph::{ChcDirectedGraph, ChcGraphError};
use crate::pdr::counterexample::Counterexample;
use crate::{ChcProblem, InvariantModel};

use super::{
    BackTranslator, IdentityBackTranslator, TransformMemoryReport, TransformObligation,
    TransformationResult, Transformer,
};

#[derive(Debug, Clone, Default)]
pub(crate) struct MultiEdgeMerger {
    verbose: bool,
}

impl MultiEdgeMerger {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }
}

impl Transformer for MultiEdgeMerger {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        // Snapshot before the graph consumes the problem, for ground
        // back-translation only.
        let input_snapshot = if crate::ground_derivation::ground_backtranslation_enabled() {
            problem.clone()
        } else {
            ChcProblem::new()
        };
        let mut graph = match ChcDirectedGraph::try_from_problem(&problem) {
            Ok(graph) => graph,
            Err(ChcGraphError::NonLinearClause { .. }) => {
                return TransformationResult {
                    problem,
                    back_translator: Box::new(IdentityBackTranslator),
                };
            }
            Err(err) => {
                if self.verbose {
                    safe_eprintln!("CHC multi-edge merge skipped: {err}");
                }
                return TransformationResult {
                    problem,
                    back_translator: Box::new(IdentityBackTranslator),
                };
            }
        };

        let merged = graph.merge_parallel_edges();
        if merged.is_empty() {
            // Nothing merged: keep the input problem byte-identical instead of
            // rebuilding it through the graph round-trip.
            return TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            };
        }
        if self.verbose {
            let removed: usize = merged.iter().map(|entry| entry.removed.len()).sum();
            safe_eprintln!(
                "CHC multi-edge merge: merged {} edge groups, removed {} clauses",
                merged.len(),
                removed
            );
        }
        let (problem, clause_origins) = graph.to_problem_with_clause_origins();
        // Retained for ground back-translation: `clause_origins` is exactly the
        // candidate table the ground translator needs, INCLUDING the merged
        // clauses with several origins that `translate_clause_index` has to
        // give up on — the ground translator picks the origin that actually
        // reproduces the step, which is a decision rather than a guess.
        let input_problem = crate::ground_derivation::ground_backtranslation_enabled()
            .then(|| std::sync::Arc::new(input_snapshot));
        TransformationResult {
            problem,
            back_translator: Box::new(MultiEdgeBackTranslator {
                clause_origins,
                input_problem,
            }),
        }
    }
}

#[derive(Debug, Clone, Default)]
struct MultiEdgeBackTranslator {
    clause_origins: Vec<Vec<usize>>,
    /// The INPUT problem, retained for ground back-translation only.
    input_problem: Option<std::sync::Arc<crate::ChcProblem>>,
}

impl MultiEdgeBackTranslator {
    fn translate_clause_index(&self, clause_index: usize) -> Option<usize> {
        match self.clause_origins.get(clause_index).map(Vec::as_slice) {
            Some([origin]) => Some(*origin),
            _ => None,
        }
    }
}

impl BackTranslator for MultiEdgeBackTranslator {
    fn translate_ground_derivation(
        &self,
        derivation: &crate::ground_derivation::GroundDerivation,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        crate::ground_derivation::clause_map::ClauseMapGroundTranslator::new(
            "multi-edge-merger",
            self.input_problem.clone()?,
            self.clause_origins.clone(),
        )
        .translate(derivation)
    }

    fn ground_translation_name(&self) -> &'static str {
        "multi-edge-merger"
    }

    fn translate_validity(&self, witness: InvariantModel) -> InvariantModel {
        witness
    }

    fn translate_invalidity(&self, mut witness: Counterexample) -> Counterexample {
        for step in &mut witness.steps {
            if let Some(clause_index) = step.clause_index {
                step.clause_index = self.translate_clause_index(clause_index);
            }
        }
        if let Some(derivation) = &mut witness.witness {
            if let Some(query_clause) = derivation.query_clause {
                derivation.query_clause = self.translate_clause_index(query_clause);
            }
            for entry in &mut derivation.entries {
                if let Some(incoming_clause) = entry.incoming_clause {
                    entry.incoming_clause = self.translate_clause_index(incoming_clause);
                }
            }
        }
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "multi_edge_merger",
            [
                TransformObligation::named("merged-clause-origin-map"),
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("original-replay-on-unsafe"),
            ],
        )
    }
}

#[cfg(test)]
mod tests {
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    use super::*;
    use crate::pdr::counterexample::{
        CounterexampleStep, DerivationWitness, DerivationWitnessEntry,
    };
    use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};

    fn int_var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    fn mergeable_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        for value in [0, 1] {
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(p, vec![int_var("x")])],
                    Some(ChcExpr::eq(int_var("x"), ChcExpr::int(value))),
                ),
                ClauseHead::Predicate(q, vec![int_var("x")]),
            ));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![int_var("x")])],
                Some(ChcExpr::lt(int_var("x"), ChcExpr::int(0))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn transformer_merges_parallel_edges() {
        let problem = mergeable_problem();
        let result = Box::new(MultiEdgeMerger::new()).transform(problem);
        assert_eq!(result.problem.clauses().len(), 2);

        let merged_clause = &result.problem.clauses()[0];
        assert!(matches!(
            merged_clause.body.constraint.as_ref(),
            Some(ChcExpr::Op(ChcOp::Or, args)) if args.len() == 2
        ));
    }

    #[test]
    fn transformer_noops_for_nonlinear_clauses() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![]);
        let q = problem.declare_predicate("Q", vec![]);
        let r = problem.declare_predicate("R", vec![]);
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![]), (q, vec![])]),
            ClauseHead::Predicate(r, vec![]),
        ));

        let result = Box::new(MultiEdgeMerger::new()).transform(problem);
        assert_eq!(result.problem.clauses().len(), 1);
    }

    #[test]
    fn backtranslator_keeps_unmerged_clause_indices_and_clears_ambiguous_merged_indices() {
        let problem = mergeable_problem();
        let result = Box::new(MultiEdgeMerger::new()).transform(problem);

        let cex = Counterexample::new(vec![
            CounterexampleStep::new(PredicateId::new(0), FxHashMap::default()).with_clause(0),
            CounterexampleStep::new(PredicateId::new(1), FxHashMap::default()).with_clause(1),
        ]);
        let translated = result.back_translator.translate_invalidity(cex);
        assert_eq!(translated.steps[0].clause_index, None);
        assert_eq!(translated.steps[1].clause_index, Some(2));
    }

    #[test]
    fn backtranslator_updates_derivation_clause_indices() {
        let problem = mergeable_problem();
        let result = Box::new(MultiEdgeMerger::new()).transform(problem);
        let witness = Counterexample {
            steps: Vec::new(),
            witness: Some(DerivationWitness {
                query_clause: Some(1),
                root: 0,
                entries: vec![DerivationWitnessEntry {
                    predicate: PredicateId::new(1),
                    level: 0,
                    state: ChcExpr::Bool(true),
                    incoming_clause: Some(0),
                    premises: Vec::new(),
                    instances: FxHashMap::default(),
                }],
            }),
            compact_derivation: None,
            ground_derivation: None,
        };
        let translated = result.back_translator.translate_invalidity(witness);
        let derivation = translated.witness.unwrap();
        assert_eq!(derivation.query_clause, Some(2));
        assert_eq!(derivation.entries[0].incoming_clause, None);
    }

    /// `P(x) <= x = init.  P(x) /\ x = 0 => Q(x).  P(x) /\ x = 5 => Q(x).
    /// Q(x) /\ x > 1 => false.` The two `P -> Q` edges (input clauses 1 and
    /// 2) merge into one clause.
    fn two_edge_problem(init: i64) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(int_var("x"), ChcExpr::int(init))),
            ClauseHead::Predicate(p, vec![int_var("x")]),
        ));
        for value in [0, 5] {
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(p, vec![int_var("x")])],
                    Some(ChcExpr::eq(int_var("x"), ChcExpr::int(value))),
                ),
                ClauseHead::Predicate(q, vec![int_var("x")]),
            ));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(q, vec![int_var("x")])],
                Some(ChcExpr::gt(int_var("x"), ChcExpr::int(1))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    /// `P(init), Q(init), false` over the merged problem.
    fn merged_derivation(
        merged: &ChcProblem,
        init: i64,
    ) -> crate::ground_derivation::GroundDerivation {
        use crate::ground_derivation::{GroundDerivation, GroundDerivationStep};
        let index = |pick: &dyn Fn(&HornClause) -> bool| {
            merged
                .clauses()
                .iter()
                .position(pick)
                .expect("the merged problem keeps every role")
        };
        let fact = index(&|clause| clause.body.predicates.is_empty());
        let edge =
            index(&|clause| matches!(clause.body.constraint, Some(ChcExpr::Op(ChcOp::Or, _))));
        let query = index(&HornClause::is_query);
        let env = || {
            [("x".to_string(), crate::smt::SmtValue::Int(init.into()))]
                .into_iter()
                .collect::<FxHashMap<_, _>>()
        };
        GroundDerivation {
            steps: vec![
                GroundDerivationStep {
                    clause_index: fact,
                    env: env(),
                    premises: vec![],
                },
                GroundDerivationStep {
                    clause_index: edge,
                    env: env(),
                    premises: vec![0],
                },
                GroundDerivationStep {
                    clause_index: query,
                    env: env(),
                    premises: vec![1],
                },
            ],
            query_step: 2,
        }
    }

    /// A merged step maps back to the edge its environment satisfies, even
    /// when that edge is not the first candidate. Every candidate completes
    /// (`x` is bound), so picking the first one that completes chose the
    /// `x = 0` edge and the translation failed its own validation.
    #[test]
    fn ground_translation_takes_the_merged_edge_the_step_satisfies() {
        let problem = two_edge_problem(5);
        let result = Box::new(MultiEdgeMerger::new()).transform(problem.clone());
        assert_eq!(result.problem.clauses().len(), 3, "the two edges merge");
        let derivation = merged_derivation(&result.problem, 5);
        crate::ground_derivation::validate_ground_derivation(&result.problem, &derivation)
            .expect("setup: the derivation validates on the merged problem");

        let translated = result
            .back_translator
            .translate_ground_derivation(&derivation)
            .expect("the `x = 5` edge carries the merged step");
        assert_eq!(translated.steps[1].clause_index, 2, "the `x = 5` edge");
        crate::ground_derivation::validate_ground_derivation(&problem, &translated)
            .expect("the translation validates on the input problem");
    }

    /// Negative twin: from `P(7)` neither edge fires, so no merged step is
    /// valid, and the candidate that only completes is still refused.
    #[test]
    fn ground_translation_refuses_a_merged_step_no_edge_satisfies() {
        let problem = two_edge_problem(7);
        let result = Box::new(MultiEdgeMerger::new()).transform(problem);
        let derivation = merged_derivation(&result.problem, 7);
        assert!(
            result
                .back_translator
                .translate_ground_derivation(&derivation)
                .is_none(),
            "no edge satisfies x = 7, so nothing is translated"
        );
    }

    #[test]
    fn transformer_preserves_action_boundaries() {
        let mut problem = ChcProblem::new();
        let a0 = problem.declare_action("A0");
        let a1 = problem.declare_action("A1");
        let p = problem.declare_predicate("P", vec![]);
        let q = problem.declare_predicate("Q", vec![]);
        problem.add_clause_with_action(
            HornClause::new(
                ClauseBody::predicates_only(vec![(p, vec![])]),
                ClauseHead::Predicate(q, vec![]),
            ),
            a0,
        );
        problem.add_clause_with_action(
            HornClause::new(
                ClauseBody::predicates_only(vec![(p, vec![])]),
                ClauseHead::Predicate(q, vec![]),
            ),
            a1,
        );

        let result = Box::new(MultiEdgeMerger::new()).transform(problem);
        assert_eq!(result.problem.clauses().len(), 2);
        assert_eq!(result.problem.clauses()[0].action_id, Some(a0));
        assert_eq!(result.problem.clauses()[1].action_id, Some(a1));
    }
}
