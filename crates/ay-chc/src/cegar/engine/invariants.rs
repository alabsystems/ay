// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Invariant extraction: disjunctive/conjunctive strategies, model building, and verification.

use super::*;

impl CegarEngine {
    pub(super) fn extract_invariants(&self) -> CegarResult {
        // Try four extraction strategies in order of preference:
        // max-states disjunctive, max-states conjunctive,
        // active-states disjunctive, active-states conjunctive.
        let strategies: &[(&FxHashMap<PredicateId, FxHashSet<AbstractState>>, bool)] = &[
            (&self.max_states, true),
            (&self.max_states, false),
            (&self.active_states, true),
            (&self.active_states, false),
        ];

        for &(states_map, disjunctive) in strategies {
            let invariants = self.extract_invariants_from(states_map, disjunctive);
            let model = self.build_model_from_invariants(&invariants);
            if self.verify_invariant_model(&model) {
                return CegarResult::Safe(model);
            }
        }

        if self.config.base.verbose {
            safe_eprintln!(
                "CEGAR: extracted models failed verification (max+active, disjunctive+conjunctive), returning Unknown"
            );
        }
        CegarResult::Unknown
    }

    /// Extract invariant formulas from a state map.
    ///
    /// When `disjunctive` is true, each relation maps to the disjunction of
    /// per-state conjunctions. When false, collects all unique predicates
    /// across states into a single conjunction per relation.
    fn extract_invariants_from(
        &self,
        states_map: &FxHashMap<PredicateId, FxHashSet<AbstractState>>,
        disjunctive: bool,
    ) -> FxHashMap<PredicateId, ChcExpr> {
        let mut invariants = FxHashMap::default();

        for (relation, states) in states_map {
            if disjunctive {
                if states.is_empty() {
                    invariants.insert(*relation, ChcExpr::Bool(true));
                    continue;
                }
                let disjuncts: Vec<_> = states
                    .iter()
                    .map(|state| {
                        if state.predicates.is_empty() {
                            ChcExpr::Bool(true)
                        } else {
                            let conjuncts: Vec<_> = state
                                .predicates
                                .iter()
                                .filter_map(|&pid| {
                                    self.predicates.get(pid).map(|p| p.formula.clone())
                                })
                                .collect();
                            ChcExpr::and_all(conjuncts)
                        }
                    })
                    .collect();
                invariants.insert(*relation, ChcExpr::or_all(disjuncts));
            } else {
                let mut unique_predicates: FxHashSet<usize> = FxHashSet::default();
                for state in states {
                    for &pid in &state.predicates {
                        unique_predicates.insert(pid);
                    }
                }
                if unique_predicates.is_empty() {
                    invariants.insert(*relation, ChcExpr::Bool(true));
                    continue;
                }
                let conjuncts: Vec<_> = unique_predicates
                    .into_iter()
                    .filter_map(|pid| self.predicates.get(pid).map(|p| p.formula.clone()))
                    .collect();
                invariants.insert(*relation, ChcExpr::and_all(conjuncts));
            }
        }

        invariants
    }

    fn build_model_from_invariants(
        &self,
        invariants: &FxHashMap<PredicateId, ChcExpr>,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            if let Some(formula) = invariants.get(&pred.id) {
                model.set(
                    pred.id,
                    PredicateInterpretation::new(self.canonical_vars(pred.id), formula.clone()),
                );
            }
        }
        model
    }

    fn verify_invariant_model(&self, model: &InvariantModel) -> bool {
        // #8630: Propagate cancellation token and add solve_timeout so
        // verification bails when the portfolio is cancelled or timed out.
        let mut verifier = PdrSolver::new(
            self.problem.clone(),
            PdrConfig {
                verbose: self.config.base.verbose,
                cancellation_token: self.config.base.cancellation_token.clone(),
                solve_timeout: Some(std::time::Duration::from_secs(30)),
                ..PdrConfig::default()
            },
        );

        verifier.verify_model(model)
    }
}
