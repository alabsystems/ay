// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition system encoding for reachability checking.
//!
//! Encodes CHC problems as init/transition/query formulas for bounded model checking
//! of counterexample traces.

use super::*;

impl PdrSolver {
    pub(in crate::pdr) fn transition_system_encoding(
        &self,
    ) -> Option<(PredicateId, Vec<ChcVar>, ChcExpr, ChcExpr, ChcExpr)> {
        // Must have exactly one predicate.
        if self.problem.predicates().len() != 1 {
            return None;
        }
        let pred_id = self.problem.predicates().first()?.id;

        // Must have at least one fact (init) and one query.
        // Transition-free systems still admit depth-0 counterexamples when an
        // initial state directly violates the query.
        if self.problem.facts().count() == 0 || self.problem.queries().count() == 0 {
            return None;
        }

        // Each transition must involve only the single predicate.
        let transitions_ok = self.problem.transitions().all(|t| {
            t.body.predicates.len() == 1
                && t.body.predicates[0].0 == pred_id
                && t.head.predicate_id() == Some(pred_id)
        });
        if !transitions_ok {
            return None;
        }

        let state_vars: Vec<ChcVar> = self.canonical_vars(pred_id)?.to_vec();
        if state_vars.is_empty() {
            return None;
        }

        let next_vars: Vec<ChcVar> = state_vars
            .iter()
            .map(|v| ChcVar::new(format!("{}_next", v.name), v.sort.clone()))
            .collect();

        let or_all = |parts: Vec<ChcExpr>| -> ChcExpr {
            parts
                .into_iter()
                .reduce(ChcExpr::or)
                .unwrap_or(ChcExpr::Bool(false))
        };

        // Extract init constraint (facts).
        let mut init_constraints = Vec::new();
        for fact in self.problem.facts() {
            if fact.head.predicate_id() != Some(pred_id) {
                continue;
            }
            let crate::ClauseHead::Predicate(_, args) = &fact.head else {
                continue;
            };
            if args.len() != state_vars.len() {
                return None;
            }

            let mut constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let mut substitutions = Vec::new();
            let mut arg_var_to_state: FxHashMap<ChcVar, ChcVar> = FxHashMap::default();
            for (i, arg) in args.iter().enumerate() {
                match arg {
                    ChcExpr::Var(orig_var) => {
                        let state_var = state_vars[i].clone();
                        if orig_var.sort != state_var.sort {
                            return None;
                        }
                        if let Some(existing) = arg_var_to_state.get(orig_var) {
                            if existing.sort != state_var.sort {
                                return None;
                            }
                            constraint = ChcExpr::and(
                                constraint,
                                ChcExpr::eq(
                                    ChcExpr::var(state_var.clone()),
                                    ChcExpr::var(existing.clone()),
                                ),
                            );
                        } else {
                            arg_var_to_state.insert(orig_var.clone(), state_var.clone());
                            substitutions.push((orig_var.clone(), ChcExpr::var(state_var)));
                        }
                    }
                    ChcExpr::Int(val) => {
                        constraint = ChcExpr::and(
                            constraint,
                            ChcExpr::eq(ChcExpr::var(state_vars[i].clone()), ChcExpr::Int(*val)),
                        );
                    }
                    _ => return None,
                }
            }
            init_constraints.push(constraint.substitute(&substitutions));
        }
        let init = or_all(init_constraints);

        // Extract transition constraint.
        let mut transition_constraints = Vec::new();
        for trans in self.problem.transitions() {
            if trans.head.predicate_id() != Some(pred_id) {
                continue;
            }
            let crate::ClauseHead::Predicate(_, head_args) = &trans.head else {
                continue;
            };
            let (_body_pred, body_args) = &trans.body.predicates[0];
            if body_args.len() != state_vars.len() || head_args.len() != state_vars.len() {
                return None;
            }

            let mut constraint = trans.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let mut substitutions = Vec::new();
            let mut arg_var_to_state: FxHashMap<ChcVar, ChcVar> = FxHashMap::default();
            let mut arg_var_to_next: FxHashMap<ChcVar, ChcVar> = FxHashMap::default();

            // Body args -> state vars (current state)
            for (i, arg) in body_args.iter().enumerate() {
                match arg {
                    ChcExpr::Var(orig_var) => {
                        let state_var = state_vars[i].clone();
                        if orig_var.sort != state_var.sort {
                            return None;
                        }
                        if let Some(existing) = arg_var_to_state.get(orig_var) {
                            if existing.sort != state_var.sort {
                                return None;
                            }
                            constraint = ChcExpr::and(
                                constraint,
                                ChcExpr::eq(
                                    ChcExpr::var(state_var.clone()),
                                    ChcExpr::var(existing.clone()),
                                ),
                            );
                        } else {
                            arg_var_to_state.insert(orig_var.clone(), state_var.clone());
                            substitutions.push((orig_var.clone(), ChcExpr::var(state_var)));
                        }
                    }
                    ChcExpr::Int(val) => {
                        constraint = ChcExpr::and(
                            constraint,
                            ChcExpr::eq(ChcExpr::var(state_vars[i].clone()), ChcExpr::Int(*val)),
                        );
                    }
                    _ => return None,
                }
            }

            // Head args -> next vars (next state)
            for (i, arg) in head_args.iter().enumerate() {
                match arg {
                    ChcExpr::Var(orig_var) => {
                        let next_var = next_vars[i].clone();
                        if orig_var.sort != next_var.sort {
                            return None;
                        }
                        // Check if already mapped in body args (i.e. unchanged var)
                        if let Some(mapped_state) = arg_var_to_state.get(orig_var) {
                            // x' = x  (variable unchanged in transition)
                            constraint = ChcExpr::and(
                                constraint,
                                ChcExpr::eq(
                                    ChcExpr::var(next_var),
                                    ChcExpr::var(mapped_state.clone()),
                                ),
                            );
                        } else if let Some(existing) = arg_var_to_next.get(orig_var) {
                            if existing.sort != next_var.sort {
                                return None;
                            }
                            constraint = ChcExpr::and(
                                constraint,
                                ChcExpr::eq(
                                    ChcExpr::var(next_var.clone()),
                                    ChcExpr::var(existing.clone()),
                                ),
                            );
                        } else {
                            arg_var_to_next.insert(orig_var.clone(), next_var.clone());
                            substitutions.push((orig_var.clone(), ChcExpr::var(next_var)));
                        }
                    }
                    ChcExpr::Int(val) => {
                        constraint = ChcExpr::and(
                            constraint,
                            ChcExpr::eq(ChcExpr::var(next_vars[i].clone()), ChcExpr::Int(*val)),
                        );
                    }
                    expr => {
                        // Expression assignment: next_var = expr (after substitution)
                        let sub_expr = expr.substitute(&substitutions);
                        constraint = ChcExpr::and(
                            constraint,
                            ChcExpr::eq(ChcExpr::var(next_vars[i].clone()), sub_expr),
                        );
                    }
                }
            }
            transition_constraints.push(constraint.substitute(&substitutions));
        }
        let transition = or_all(transition_constraints);

        // Extract query constraint.
        let mut query_constraints = Vec::new();
        for query_clause in self.problem.queries() {
            if query_clause.body.predicates.len() != 1 {
                continue;
            }
            let (_body_pred, body_args) = &query_clause.body.predicates[0];
            if body_args.len() != state_vars.len() {
                return None;
            }
            let mut constraint = query_clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let mut substitutions = Vec::new();
            let mut arg_var_to_state: FxHashMap<ChcVar, ChcVar> = FxHashMap::default();
            for (i, arg) in body_args.iter().enumerate() {
                match arg {
                    ChcExpr::Var(orig_var) => {
                        let state_var = state_vars[i].clone();
                        if orig_var.sort != state_var.sort {
                            return None;
                        }
                        if let Some(existing) = arg_var_to_state.get(orig_var) {
                            if existing.sort != state_var.sort {
                                return None;
                            }
                            constraint = ChcExpr::and(
                                constraint,
                                ChcExpr::eq(
                                    ChcExpr::var(state_var.clone()),
                                    ChcExpr::var(existing.clone()),
                                ),
                            );
                        } else {
                            arg_var_to_state.insert(orig_var.clone(), state_var.clone());
                            substitutions.push((orig_var.clone(), ChcExpr::var(state_var)));
                        }
                    }
                    ChcExpr::Int(val) => {
                        constraint = ChcExpr::and(
                            constraint,
                            ChcExpr::eq(ChcExpr::var(state_vars[i].clone()), ChcExpr::Int(*val)),
                        );
                    }
                    _ => return None,
                }
            }
            query_constraints.push(constraint.substitute(&substitutions));
        }
        let query = or_all(query_constraints);

        Some((pred_id, state_vars, init, transition, query))
    }

    pub(in crate::pdr) fn encode_transition_system_reachability(
        state_vars: &[ChcVar],
        init: &ChcExpr,
        transition: &ChcExpr,
        query: &ChcExpr,
        depth: usize,
    ) -> ChcExpr {
        fn version_var(var: &ChcVar, t: usize) -> ChcVar {
            if t == 0 {
                var.clone()
            } else {
                ChcVar::new(format!("{}_{}", var.name, t), var.sort.clone())
            }
        }

        fn version_and_freshen(
            expr: &ChcExpr,
            state_vars: &[ChcVar],
            t: usize,
            label: &str,
        ) -> ChcExpr {
            let state_by_name: FxHashMap<String, ChcVar> = state_vars
                .iter()
                .cloned()
                .map(|v| (v.name.clone(), v))
                .collect();
            let next_by_name: FxHashMap<String, ChcVar> = state_vars
                .iter()
                .cloned()
                .map(|v| (format!("{}_next", v.name), v))
                .collect();

            let subst: Vec<(ChcVar, ChcExpr)> = expr
                .vars()
                .into_iter()
                .map(|v| {
                    if let Some(base) = state_by_name.get(&v.name) {
                        let new_v = version_var(base, t);
                        (v, ChcExpr::var(new_v))
                    } else if let Some(base) = next_by_name.get(&v.name) {
                        let new_v = version_var(base, t + 1);
                        (v, ChcExpr::var(new_v))
                    } else {
                        let new_v = ChcVar::new(format!("{}__{}", v.name, label), v.sort.clone());
                        (v, ChcExpr::var(new_v))
                    }
                })
                .collect();

            if subst.is_empty() {
                return expr.clone();
            }
            expr.substitute(&subst)
        }

        let mut conjuncts = Vec::with_capacity(depth + 2);
        conjuncts.push(version_and_freshen(init, state_vars, 0, "init"));
        for i in 0..depth {
            conjuncts.push(version_and_freshen(
                transition,
                state_vars,
                i,
                &format!("trans{i}"),
            ));
        }
        conjuncts.push(version_and_freshen(query, state_vars, depth, "query"));

        ChcExpr::and_all(conjuncts)
    }
}
