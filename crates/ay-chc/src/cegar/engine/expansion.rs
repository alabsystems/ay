// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! State generation, edge creation, and match enumeration for CEGAR.
//!
//! Contains the expansion logic that generates abstract states from SMT
//! implication checks, adds edges to the ARG, discovers new clause matches,
//! and enumerates feasible state combinations for multi-body clauses.

use super::{
    AbstractEdge, AbstractState, CachedFeasibility, CegarEngine, ChcExpr, ChcOp, ClauseHead,
    PredicateId, SmtResult,
};
use crate::pdr::implication_cache::SmallModel;

impl CegarEngine {
    pub(super) fn try_generate_edge(
        &mut self,
        from: &[AbstractState],
        clause_index: usize,
        assumptions: &ChcExpr,
    ) -> Option<AbstractEdge> {
        // SOUNDNESS NOTE (#2659): Unknown → treat as Sat is intentionally over-approximate.
        // CEGAR builds an abstract transition system where extra edges cause spurious
        // counterexamples that refinement eliminates. Treating Unknown as infeasible
        // (Unsat) would risk missing real counterexamples — unsound for CEGAR.

        // State preservation (#3762): check the feasibility cache before querying SMT.
        let sat = if let Some(cached) = self.cache.check_feasibility(assumptions) {
            !matches!(cached, CachedFeasibility::Unsat)
        } else {
            let result = self
                .smt
                .check_sat_with_timeout(assumptions, self.config.query_timeout);
            let feasibility = match &result {
                SmtResult::Sat(_) => CachedFeasibility::Sat,
                SmtResult::Unknown => CachedFeasibility::Unknown,
                _ => CachedFeasibility::Unsat,
            };
            self.cache
                .store_feasibility(assumptions.clone(), feasibility);
            matches!(result, SmtResult::Sat(_) | SmtResult::Unknown)
        };

        if !sat {
            return None;
        }

        let clause = &self.problem.clauses()[clause_index];
        let head_info = match &clause.head {
            ClauseHead::False => None,
            ClauseHead::Predicate(pred_id, head_args) => Some((*pred_id, head_args.clone())),
        };
        match head_info {
            None => Some(AbstractEdge::new(
                from.to_vec(),
                AbstractState::new(PredicateId(u32::MAX), vec![]),
                clause_index,
            )),
            Some((pred_id, head_args)) => {
                let state = self.generate_abstract_state(pred_id, &head_args, assumptions);
                Some(AbstractEdge::new(from.to_vec(), state, clause_index))
            }
        }
    }

    fn generate_abstract_state(
        &mut self,
        relation: PredicateId,
        head_args: &[ChcExpr],
        assumptions: &ChcExpr,
    ) -> AbstractState {
        let pred_ids: Vec<usize> = self.predicates.predicates_for_relation(relation).to_vec();

        if pred_ids.is_empty() {
            return AbstractState::new(relation, vec![]);
        }

        let canonical_vars = self.canonical_vars(relation);
        let subst: Vec<_> = canonical_vars
            .iter()
            .zip(head_args.iter())
            .map(|(v, arg)| (v.clone(), arg.clone()))
            .collect();

        // Phase 1: Get a model of the assumptions and use it to partition
        // predicates into definitely-false (exclude), definitely-true (include
        // via model), and unknown (need SMT check).
        let model = self.smt.get_model(assumptions);
        let eval_model = model.as_ref().map(SmallModel::from_smt_model);

        let mut implied = Vec::new();
        let mut need_smt_check: Vec<(usize, ChcExpr)> = Vec::new();

        for pred_id in pred_ids {
            let pred_formula = match self.predicates.get(pred_id) {
                Some(p) => p.formula.clone(),
                None => continue,
            };

            let concrete_pred = pred_formula.substitute(&subst);

            if let Some(ref eval) = eval_model {
                match eval.evaluate(&concrete_pred) {
                    Some(false) => continue, // Definitely not implied
                    Some(true) => {
                        // True in this model — needs SMT check to confirm implication
                        need_smt_check.push((pred_id, concrete_pred));
                    }
                    None => {
                        // Could not evaluate — needs SMT check
                        need_smt_check.push((pred_id, concrete_pred));
                    }
                }
            } else {
                need_smt_check.push((pred_id, concrete_pred));
            }
        }

        // Phase 2: Run SMT implication checks only for candidates.
        // Sort: equality predicates first (most discriminating for subsumption),
        // then others. Cap to prevent abstraction from dominating runtime.
        need_smt_check.sort_by_key(|(_, expr)| {
            if matches!(expr, ChcExpr::Op(ChcOp::Eq, _)) {
                0
            } else {
                1
            }
        });
        let smt_check_limit = 24;
        for (pred_id, concrete_pred) in need_smt_check.iter().take(smt_check_limit) {
            // State preservation (#3762): check the implication cache first.
            let implies = if let Some(cached) =
                self.cache.check_implication(assumptions, concrete_pred)
            {
                cached
            } else {
                let result = self.smt.check_implies(assumptions, concrete_pred);
                self.cache
                    .store_implication(assumptions.clone(), concrete_pred.clone(), result);
                result
            };
            if implies {
                implied.push(*pred_id);
            }
        }
        // Skip predicates beyond the limit to stay conservative.
        // Missing some implied predicates creates less refined states,
        // but that's safe: fewer predicates = more general = subsumes more.

        AbstractState::new(relation, implied)
    }

    pub(super) fn add_edge(&mut self, edge: AbstractEdge) {
        let to_state = edge.to.clone();
        self.edges.push(edge);
        self.add_state(to_state);
    }

    fn add_state(&mut self, state: AbstractState) {
        if self.forward_subsumed.contains_key(&state) {
            return;
        }

        let relation = state.relation;

        if let Some(active) = self.active_states.get(&relation) {
            if active.contains(&state) {
                return;
            }
            // Enforce max_states_per_relation to prevent unbounded memory growth
            if active.len() >= self.config.max_states_per_relation {
                if self.config.base.verbose {
                    safe_eprintln!(
                        "CEGAR: state limit reached for relation {} ({} states)",
                        relation.index(),
                        active.len()
                    );
                }
                return;
            }
        }

        if let Some(max_set) = self.max_states.get(&relation) {
            if let Some(subsuming) = max_set.iter().find(|s| s.subsumes(&state)).cloned() {
                self.forward_subsumed.insert(state, subsuming);
                return;
            }
        }

        let subsumed: Vec<_> = self
            .max_states
            .get(&relation)
            .map(|ms| ms.iter().filter(|s| state.subsumes(s)).cloned().collect())
            .unwrap_or_default();

        if let Some(max_set) = self.max_states.get_mut(&relation) {
            for s in &subsumed {
                max_set.remove(s);
                self.backward_subsumed.insert(s.clone(), state.clone());
            }
        }

        self.queue.inc_time();
        self.find_new_matches(&state);

        self.active_states
            .entry(relation)
            .or_default()
            .insert(state.clone());
        self.max_states.entry(relation).or_default().insert(state);
    }

    fn find_new_matches(&mut self, state: &AbstractState) {
        let relation = state.relation;

        let clause_info: Vec<_> = self
            .problem
            .clauses()
            .iter()
            .enumerate()
            .filter_map(|(clause_idx, clause)| {
                let body_preds = &clause.body.predicates;
                let matching_positions: Vec<_> = body_preds
                    .iter()
                    .enumerate()
                    .filter(|(_, (pid, _))| *pid == relation)
                    .map(|(i, _)| i)
                    .collect();

                if matching_positions.is_empty() {
                    return None;
                }

                let is_query = clause.head.is_query();
                Some((clause_idx, body_preds.len(), matching_positions, is_query))
            })
            .collect();

        for (clause_idx, body_len, matching_positions, is_query) in clause_info {
            for &body_idx in &matching_positions {
                if body_len == 1 {
                    let body_states = vec![state.clone()];
                    let assumptions = self.build_expansion_constraint(clause_idx, &body_states);
                    // State preservation (#3762): check the feasibility cache.
                    let feasible = if let Some(cached) = self.cache.check_feasibility(&assumptions)
                    {
                        !matches!(cached, CachedFeasibility::Unsat)
                    } else {
                        let result = self
                            .smt
                            .check_sat_with_timeout(&assumptions, self.config.query_timeout);
                        let feasibility = match &result {
                            SmtResult::Sat(_) => CachedFeasibility::Sat,
                            SmtResult::Unknown => CachedFeasibility::Unknown,
                            _ => CachedFeasibility::Unsat,
                        };
                        self.cache.store_feasibility(assumptions, feasibility);
                        matches!(result, SmtResult::Sat(_) | SmtResult::Unknown)
                    };
                    if feasible {
                        self.queue.enqueue(body_states, clause_idx, is_query);
                    }
                    continue;
                }

                let body_predicates = self.problem.clauses()[clause_idx].body.predicates.clone();
                let combinations = self.enumerate_state_combinations(
                    clause_idx,
                    &body_predicates,
                    body_idx,
                    state,
                );
                for combo in combinations {
                    self.queue.enqueue(combo, clause_idx, is_query);
                }
            }
        }
    }

    pub(super) fn enumerate_state_combinations(
        &mut self,
        clause_index: usize,
        body_predicates: &[(PredicateId, Vec<ChcExpr>)],
        fixed_idx: usize,
        fixed_state: &AbstractState,
    ) -> Vec<Vec<AbstractState>> {
        const MAX_STATES_PER_POSITION: usize = 32;
        const MAX_COMBINATIONS: usize = 256;

        if body_predicates.is_empty() || fixed_idx >= body_predicates.len() {
            return vec![];
        }

        let mut assignments = vec![None; body_predicates.len()];
        assignments[fixed_idx] = Some(fixed_state.clone());

        let mut candidates: Vec<(usize, Vec<AbstractState>)> = Vec::new();
        for (idx, (pred_id, _)) in body_predicates.iter().enumerate() {
            if idx == fixed_idx {
                continue;
            }
            let active = match self.active_states.get(pred_id) {
                Some(s) if !s.is_empty() => s,
                _ => return vec![],
            };
            let mut states: Vec<_> = active.iter().cloned().collect();
            states.sort_by_key(|s| s.predicates.len());
            states.truncate(MAX_STATES_PER_POSITION);
            candidates.push((idx, states));
        }
        candidates.sort_by_key(|(_, states)| states.len());

        let mut results = Vec::new();
        self.collect_feasible_combinations(
            clause_index,
            &candidates,
            0,
            &mut assignments,
            &mut results,
            MAX_COMBINATIONS,
        );
        results
    }

    fn collect_feasible_combinations(
        &mut self,
        clause_index: usize,
        candidates: &[(usize, Vec<AbstractState>)],
        depth: usize,
        assignments: &mut [Option<AbstractState>],
        results: &mut Vec<Vec<AbstractState>>,
        max_combinations: usize,
    ) {
        if results.len() >= max_combinations {
            return;
        }

        if depth == candidates.len() {
            if !self.partial_assignment_is_feasible(clause_index, assignments) {
                return;
            }
            let mut combo = Vec::with_capacity(assignments.len());
            for state in assignments.iter() {
                let Some(state) = state else {
                    return;
                };
                combo.push(state.clone());
            }
            results.push(combo);
            return;
        }

        let (position, states) = &candidates[depth];
        for state in states {
            assignments[*position] = Some(state.clone());
            if self.partial_assignment_is_feasible(clause_index, assignments) {
                self.collect_feasible_combinations(
                    clause_index,
                    candidates,
                    depth + 1,
                    assignments,
                    results,
                    max_combinations,
                );
                if results.len() >= max_combinations {
                    break;
                }
            }
            assignments[*position] = None;
        }
    }

    fn partial_assignment_is_feasible(
        &mut self,
        clause_index: usize,
        assignments: &[Option<AbstractState>],
    ) -> bool {
        let assumptions = self.build_partial_expansion_constraint(clause_index, assignments);
        // State preservation (#3762): check the feasibility cache.
        if let Some(cached) = self.cache.check_feasibility(&assumptions) {
            return !matches!(cached, CachedFeasibility::Unsat);
        }
        let result = self
            .smt
            .check_sat_with_timeout(&assumptions, self.config.query_timeout);
        let feasibility = match &result {
            SmtResult::Sat(_) => CachedFeasibility::Sat,
            SmtResult::Unknown => CachedFeasibility::Unknown,
            _ => CachedFeasibility::Unsat,
        };
        self.cache.store_feasibility(assumptions, feasibility);
        matches!(result, SmtResult::Sat(_) | SmtResult::Unknown)
    }

    fn build_partial_expansion_constraint(
        &self,
        clause_index: usize,
        body_states: &[Option<AbstractState>],
    ) -> ChcExpr {
        let clause = &self.problem.clauses()[clause_index];
        let mut conjuncts = Vec::new();

        if let Some(ref constraint) = clause.body.constraint {
            conjuncts.push(constraint.clone());
        }

        for (state_idx, maybe_state) in body_states.iter().enumerate() {
            let Some(state) = maybe_state else {
                continue;
            };
            if state_idx >= clause.body.predicates.len() {
                break;
            }
            let (_pred_id, ref body_args) = clause.body.predicates[state_idx];
            let canonical_vars = self.canonical_vars(state.relation);
            for &pred_idx in &state.predicates {
                if let Some(pred) = self.predicates.get(pred_idx) {
                    let subst: Vec<_> = canonical_vars
                        .iter()
                        .zip(body_args.iter())
                        .map(|(v, arg)| (v.clone(), arg.clone()))
                        .collect();
                    conjuncts.push(pred.formula.substitute(&subst));
                }
            }
        }

        ChcExpr::and_all(conjuncts)
    }
}
