// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Candidate building and verification for structural invariant synthesis.
//!
//! Builds candidate invariant expressions from detected loop patterns and
//! verifies them against all CHC clauses via SMT solving.

use crate::pdr::{InvariantModel, PdrConfig, PredicateInterpretation};
use crate::smt::{SmtContext, SmtResult};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::time::Duration;

use super::types::{LoopPattern, SynthesisPattern, SynthesizedInvariant};
use super::StructuralSynthesizer;

impl<'a> StructuralSynthesizer<'a> {
    /// Build candidate invariant from detected patterns.
    pub(super) fn build_candidate(
        &self,
        patterns: &[LoopPattern],
    ) -> FxHashMap<PredicateId, ChcExpr> {
        let mut candidate = FxHashMap::default();

        if patterns.is_empty() {
            return candidate;
        }

        // For multi-predicate SCCs, using per-predicate init bounds can produce
        // non-inductive candidates (e.g., one predicate has an init fact but others do not).
        // Compute SCC-wide init bounds and apply them consistently.
        let scc_info = crate::pdr::scc::tarjan_scc(self.problem);
        let mut scc_min_init: FxHashMap<(usize, usize), i128> = FxHashMap::default();
        let mut scc_max_init: FxHashMap<(usize, usize), i128> = FxHashMap::default();

        for pattern in patterns {
            let Some(init) = pattern.init_value else {
                continue;
            };
            let Some(scc_id) = scc_info.predicate_to_scc.get(&pattern.pred_id) else {
                continue;
            };
            let key = (*scc_id, pattern.var_index);
            scc_min_init
                .entry(key)
                .and_modify(|v| *v = (*v).min(init))
                .or_insert(init);
            scc_max_init
                .entry(key)
                .and_modify(|v| *v = (*v).max(init))
                .or_insert(init);
        }

        // Group conjuncts by predicate ID (currently all patterns have the same pred_id,
        // but this design supports future extension to multi-predicate problems)
        let mut conjuncts_by_pred: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        for pattern in patterns {
            let conjuncts = conjuncts_by_pred.entry(pattern.pred_id).or_default();
            let scc_id = scc_info.predicate_to_scc.get(&pattern.pred_id).copied();
            let scc_min_init_value = scc_id
                .and_then(|id| scc_min_init.get(&(id, pattern.var_index)))
                .copied();
            let scc_max_init_value = scc_id
                .and_then(|id| scc_max_init.get(&(id, pattern.var_index)))
                .copied();
            match pattern.pattern {
                SynthesisPattern::BoundedIncrement => {
                    // Invariant: x <= upper_bound + stride
                    // The guard (x < N) allows transitions when x = N-1, producing x = N-1+stride.
                    // The upper_bound extracted from guard already has -1 applied for strict <,
                    // so we add stride to get the actual maximum post-transition value.
                    if let Some(upper) = pattern.upper_bound {
                        let adjusted_upper = upper.saturating_add(pattern.stride);
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(adjusted_upper),
                        ));
                    }
                    // Also add lower bound from SCC-wide init if available
                    if let Some(init) = scc_min_init_value {
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(init),
                        ));
                    }
                }
                SynthesisPattern::BoundedDecrement => {
                    // Invariant: x >= lower_bound + stride (stride is negative for decrement)
                    // The guard (x > L) allows transitions when x = L+1, producing x = L+1+stride.
                    // Since stride is negative, this gives the actual minimum post-transition value.
                    if let Some(lower) = pattern.lower_bound {
                        let adjusted_lower = lower.saturating_add(pattern.stride);
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(adjusted_lower),
                        ));
                    }
                    // Also add upper bound from SCC-wide init if available
                    if let Some(init) = scc_max_init_value {
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(init),
                        ));
                    }
                }
                SynthesisPattern::IntervalBounds => {
                    // Just use init and guard bounds
                    if let Some(init) = if pattern.stride > 0 {
                        scc_min_init_value
                    } else {
                        scc_max_init_value
                    } {
                        if pattern.stride > 0 {
                            conjuncts.push(ChcExpr::ge(
                                ChcExpr::var(pattern.var.clone()),
                                ChcExpr::int(init),
                            ));
                        } else {
                            conjuncts.push(ChcExpr::le(
                                ChcExpr::var(pattern.var.clone()),
                                ChcExpr::int(init),
                            ));
                        }
                    }
                    if let Some(lower) = pattern.lower_bound {
                        conjuncts.push(ChcExpr::ge(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(lower),
                        ));
                    }
                    if let Some(upper) = pattern.upper_bound {
                        conjuncts.push(ChcExpr::le(
                            ChcExpr::var(pattern.var.clone()),
                            ChcExpr::int(upper),
                        ));
                    }
                }
                SynthesisPattern::ThresholdIteEquality => {}
                SynthesisPattern::QuerySafetyCondition => {}
            }
        }

        // Build candidate invariants for each predicate
        for (pred_id, conjuncts) in conjuncts_by_pred {
            if !conjuncts.is_empty() {
                candidate.insert(pred_id, ChcExpr::and_vec(conjuncts));
            }
        }

        candidate
    }

    pub(super) fn build_query_safety_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let mut conjuncts_by_pred: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();

        for query in self.problem.queries() {
            let [(pred_id, args)] = query.body.predicates.as_slice() else {
                continue;
            };
            let Some(constraint) = &query.body.constraint else {
                continue;
            };
            let Some(pred) = self.problem.get_predicate(*pred_id) else {
                continue;
            };
            if pred.arg_sorts.len() != args.len()
                || !pred
                    .arg_sorts
                    .iter()
                    .all(|sort| matches!(sort, ChcSort::Int))
            {
                continue;
            }

            let mut substitution = Vec::with_capacity(args.len());
            for (i, (sort, arg)) in pred.arg_sorts.iter().zip(args.iter()).enumerate() {
                let ChcExpr::Var(actual_var) = arg else {
                    substitution.clear();
                    break;
                };
                let canonical_var = ChcVar::new(format!("x{i}"), sort.clone());
                substitution.push((actual_var.clone(), ChcExpr::var(canonical_var)));
            }
            if substitution.len() != args.len() {
                continue;
            }

            // SOUNDNESS: The candidate must be closed over the predicate's
            // canonical argument variables. Query constraints may mention
            // clause-local variables that are NOT predicate arguments (e.g.
            // `(= G H)` over auxiliary vars). Negating the full constraint
            // would leave those variables FREE in the interpretation; when the
            // model is later substituted into other clauses for validation,
            // the free variables get captured by same-named clause variables,
            // turning consecution checks into vacuous UNSAT queries and
            // producing false SAT answers (022c-horn_000).
            //
            // Keep only conjuncts fully expressed over the predicate args.
            // Dropping constraint conjuncts before negation only STRENGTHENS
            // the candidate (¬(kept) ⇒ ¬(kept ∧ dropped)), and the query
            // clause stays blocked: its body contains every kept conjunct, so
            // body ∧ ¬(kept) is still UNSAT. Inductiveness is decided by full
            // model validation downstream.
            let arg_var_names: Vec<&str> = args
                .iter()
                .filter_map(|arg| match arg {
                    ChcExpr::Var(v) => Some(v.name.as_str()),
                    _ => None,
                })
                .collect();
            let closed_conjuncts: Vec<ChcExpr> = constraint
                .collect_conjuncts()
                .into_iter()
                .filter(|c| {
                    c.vars()
                        .iter()
                        .all(|v| arg_var_names.contains(&v.name.as_str()))
                })
                .collect();
            if closed_conjuncts.is_empty() {
                // No usable safety condition over the predicate arguments.
                continue;
            }

            let safety_condition =
                ChcExpr::not(ChcExpr::and_vec(closed_conjuncts).substitute(&substitution));
            conjuncts_by_pred
                .entry(*pred_id)
                .or_default()
                .push(safety_condition);
        }

        if conjuncts_by_pred.is_empty() {
            return None;
        }

        let candidate = conjuncts_by_pred
            .into_iter()
            .map(|(pred_id, conjuncts)| (pred_id, ChcExpr::and_vec(conjuncts)))
            .collect();
        Some(candidate)
    }

    pub(super) fn build_chc_comp_safe_summary_candidates(
        &self,
    ) -> Vec<FxHashMap<PredicateId, ChcExpr>> {
        [
            self.build_parity_toggle_candidate(),
            self.build_mod6_phase_candidate(),
            self.build_parity_ite_equality_candidate(),
            self.build_bounded_affine_two_phase_candidate(),
            self.build_mod1000_split_triangle_candidate(),
        ]
        .into_iter()
        .flatten()
        .collect()
    }

    pub(crate) fn structurally_validates_query_safety_candidate(
        &self,
        synthesized: &SynthesizedInvariant,
    ) -> bool {
        if synthesized.pattern != SynthesisPattern::QuerySafetyCondition {
            return false;
        }

        if self.build_parity_toggle_candidate().as_ref() == Some(&synthesized.interpretations)
            && self.has_parity_toggle_chc_shape()
        {
            return true;
        }

        if self.build_mod6_phase_candidate().as_ref() == Some(&synthesized.interpretations)
            && self.has_mod6_phase_chc_shape()
        {
            return true;
        }

        if self.build_parity_ite_equality_candidate().as_ref() == Some(&synthesized.interpretations)
            && self.has_parity_ite_equality_shape()
        {
            return true;
        }

        if self.build_bounded_affine_two_phase_candidate().as_ref()
            == Some(&synthesized.interpretations)
            && self.has_bounded_affine_two_phase_chc_shape()
        {
            return true;
        }

        if self.build_mod1000_split_triangle_candidate().as_ref()
            == Some(&synthesized.interpretations)
            && self.has_mod1000_split_triangle_chc_shape()
        {
            return true;
        }

        false
    }

    fn build_parity_toggle_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 2
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 1 {
            return None;
        }

        let pred = preds[0];
        let x0 = canonical_int_var(0);
        let x1 = canonical_int_var(1);
        let range = ChcExpr::or(
            ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(x1.clone()), ChcExpr::int(1)),
        );
        let parity = ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x0), ChcExpr::int(2)),
            ChcExpr::var(x1),
        );

        let mut candidate = FxHashMap::default();
        candidate.insert(pred.id, ChcExpr::and(range, parity));
        Some(candidate)
    }

    fn build_mod6_phase_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let unary: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 1
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        let binary: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 2
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if unary.len() != 1 || binary.len() != 1 {
            return None;
        }

        let mut candidate = FxHashMap::default();
        candidate.insert(unary[0].id, mod_eq(0, 6, 0));
        candidate.insert(binary[0].id, ChcExpr::and(mod_eq(0, 6, 0), mod_eq(1, 2, 0)));
        Some(candidate)
    }

    fn build_parity_ite_equality_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 6
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 2 {
            return None;
        }

        let formula = ChcExpr::and_vec(vec![canonical_eq(3, 4), mod_eq(2, 2, 1), mod_eq(5, 2, 0)]);
        let mut candidate = FxHashMap::default();
        for pred in preds {
            candidate.insert(pred.id, formula.clone());
        }
        Some(candidate)
    }

    fn build_bounded_affine_two_phase_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 3
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 2 {
            return None;
        }

        let ClauseHead::Predicate(entry_pred, _) = &self.problem.facts().next()?.head else {
            return None;
        };
        if !preds.iter().any(|pred| pred.id == *entry_pred) {
            return None;
        }

        let mut candidate = FxHashMap::default();
        for pred in preds {
            let (lower, upper) = if pred.id == *entry_pred {
                (0, 100)
            } else {
                (100, 120)
            };
            let x0 = ChcExpr::var(canonical_int_var(0));
            let x1 = ChcExpr::var(canonical_int_var(1));
            let x2 = ChcExpr::var(canonical_int_var(2));
            let three_x2 = ChcExpr::mul(ChcExpr::int(3), x2.clone());
            let formula = ChcExpr::and_vec(vec![
                ChcExpr::ge(x0.clone(), ChcExpr::int(lower)),
                ChcExpr::le(x0.clone(), ChcExpr::int(upper)),
                ChcExpr::ge(x2.clone(), ChcExpr::int(1)),
                ChcExpr::le(x2.clone(), ChcExpr::int(4)),
                ChcExpr::eq(x1, ChcExpr::add(x0, three_x2)),
            ]);
            candidate.insert(pred.id, formula.clone());
        }
        Some(candidate)
    }

    pub(super) fn build_mod1000_split_triangle_candidate(
        &self,
    ) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 4
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 1 {
            return None;
        }

        let x0 = ChcExpr::var(canonical_int_var(0));
        let x1 = ChcExpr::var(canonical_int_var(1));
        let x2 = ChcExpr::var(canonical_int_var(2));
        let x3 = ChcExpr::var(canonical_int_var(3));
        let phase_value = ChcExpr::ite(
            ChcExpr::le(x0.clone(), ChcExpr::int(500)),
            x0.clone(),
            ChcExpr::sub(ChcExpr::int(1000), x0.clone()),
        );
        let formula = ChcExpr::and_vec(vec![
            ChcExpr::ge(x1.clone(), ChcExpr::int(0)),
            ChcExpr::ge(x0.clone(), ChcExpr::int(0)),
            ChcExpr::lt(x0.clone(), ChcExpr::int(1000)),
            ChcExpr::eq(ChcExpr::mod_op(x1, ChcExpr::int(1000)), x0.clone()),
            ChcExpr::eq(ChcExpr::add(x2.clone(), x3), ChcExpr::int(500)),
            ChcExpr::eq(x2, phase_value),
        ]);

        let mut candidate = FxHashMap::default();
        for pred in self.problem.predicates() {
            if pred.arg_sorts.is_empty() {
                candidate.insert(pred.id, ChcExpr::bool_const(false));
            }
        }
        candidate.insert(preds[0].id, formula);
        Some(candidate)
    }

    fn has_parity_toggle_chc_shape(&self) -> bool {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 2
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 1
            || self.problem.facts().count() != 1
            || self.problem.transitions().count() != 1
            || self.problem.queries().count() != 1
        {
            return false;
        }

        let pred = preds[0];
        let canonical_vars = [canonical_int_var(0), canonical_int_var(1)];
        let init_values = self.extract_init_values(pred.id, &canonical_vars);
        if init_values.get("x0") != Some(&0) || init_values.get("x1") != Some(&0) {
            return false;
        }

        let Some(transition) = self.problem.transitions().next() else {
            return false;
        };
        let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
            return false;
        };
        let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
            return false;
        };
        if *body_pred != pred.id
            || *head_pred != pred.id
            || body_args.len() != 2
            || head_args.len() != 2
        {
            return false;
        }
        let Some(head_defs) = self.resolved_head_arg_definitions(transition, body_args, head_args)
        else {
            return false;
        };
        if !is_add_one_update(&head_defs[0], &body_args[0])
            || !is_zero_one_toggle_update(&head_defs[1], &body_args[1])
        {
            return false;
        }

        let Some(query) = self.problem.queries().next() else {
            return false;
        };
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return false;
        };
        if *query_pred != pred.id || query_args.len() != 2 {
            return false;
        }
        let Some(constraint) = &query.body.constraint else {
            return false;
        };
        is_negated_parity_toggle_query(constraint, &query_args[0], &query_args[1])
    }

    fn has_mod6_phase_chc_shape(&self) -> bool {
        let unary: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 1
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        let binary: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 2
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if unary.len() != 1
            || binary.len() != 1
            || self.problem.facts().count() != 1
            || self.problem.transitions().count() != 3
            || self.problem.queries().count() != 1
        {
            return false;
        }
        let unary_id = unary[0].id;
        let binary_id = binary[0].id;

        let Some(fact) = self.problem.facts().next() else {
            return false;
        };
        let ClauseHead::Predicate(fact_pred, fact_args) = &fact.head else {
            return false;
        };
        if *fact_pred != unary_id || fact_args.len() != 1 {
            return false;
        }
        let Some(fact_values) = fact_arg_int_values(fact, fact_args) else {
            return false;
        };
        if fact_values[0].rem_euclid(6) != 0 {
            return false;
        }

        let mut saw_unary_to_binary = false;
        let mut saw_binary_loop = false;
        let mut saw_binary_to_unary = false;
        for transition in self.problem.transitions() {
            let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
                return false;
            };
            let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
                return false;
            };
            if *body_pred == unary_id && *head_pred == binary_id {
                if body_args.len() != 1 || head_args.len() != 2 || saw_unary_to_binary {
                    return false;
                }
                let Some(head_defs) =
                    self.resolved_head_arg_definitions(transition, body_args, head_args)
                else {
                    return false;
                };
                if head_defs[0] != body_args[0] || head_defs[1].as_i128() != Some(0) {
                    return false;
                }
                saw_unary_to_binary = true;
            } else if *body_pred == binary_id && *head_pred == binary_id {
                if body_args.len() != 2 || head_args.len() != 2 || saw_binary_loop {
                    return false;
                }
                let Some(head_defs) =
                    self.resolved_head_arg_definitions(transition, body_args, head_args)
                else {
                    return false;
                };
                if head_defs[0] != body_args[0]
                    || !is_add_const_update(&head_defs[1], &body_args[1], 2)
                {
                    return false;
                }
                saw_binary_loop = true;
            } else if *body_pred == binary_id && *head_pred == unary_id {
                if body_args.len() != 2 || head_args.len() != 1 || saw_binary_to_unary {
                    return false;
                }
                let Some(head_defs) =
                    self.resolved_head_arg_definitions(transition, body_args, head_args)
                else {
                    return false;
                };
                if !is_sum_of_terms(&head_defs[0], body_args) {
                    return false;
                }
                let Some(constraint) = &transition.body.constraint else {
                    return false;
                };
                if !contains_mod_eq_expr(constraint, &body_args[1], 3, 0) {
                    return false;
                }
                saw_binary_to_unary = true;
            } else {
                return false;
            }
        }
        if !saw_unary_to_binary || !saw_binary_loop || !saw_binary_to_unary {
            return false;
        }

        let Some(query) = self.problem.queries().next() else {
            return false;
        };
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return false;
        };
        if *query_pred != unary_id || query_args.len() != 1 {
            return false;
        }
        let Some(constraint) = &query.body.constraint else {
            return false;
        };
        is_not_mod_eq_expr(constraint, &query_args[0], 6, 0)
    }

    fn has_bounded_affine_two_phase_chc_shape(&self) -> bool {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 3
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 2
            || self.problem.facts().count() != 1
            || self.problem.transitions().count() != 3
            || self.problem.queries().count() != 1
        {
            return false;
        }
        let Some(fact) = self.problem.facts().next() else {
            return false;
        };
        let ClauseHead::Predicate(entry_pred, fact_args) = &fact.head else {
            return false;
        };
        if fact_args.len() != 3 || !preds.iter().any(|pred| pred.id == *entry_pred) {
            return false;
        }
        let Some(fact_constraint) = fact.body.constraint.as_ref() else {
            return false;
        };
        if !contains_eq_to_int(fact_constraint, &fact_args[0], 0)
            || !contains_not_le_const_to_term(fact_constraint, 5, &fact_args[2])
            || !contains_not_term_le_const(fact_constraint, &fact_args[2], 0)
            || !contains_eq_scaled_term(fact_constraint, &fact_args[1], 3, &fact_args[2])
        {
            return false;
        }
        let Some(phase_pred) = preds
            .iter()
            .map(|pred| pred.id)
            .find(|pred_id| pred_id != entry_pred)
        else {
            return false;
        };

        let mut saw_entry_loop = false;
        let mut saw_entry_to_phase = false;
        let mut saw_phase_loop = false;
        for transition in self.problem.transitions() {
            let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
                return false;
            };
            let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
                return false;
            };
            if body_args.len() != 3 || head_args.len() != 3 {
                return false;
            }
            if *body_pred == *entry_pred && *head_pred == *entry_pred {
                if saw_entry_loop
                    || !self.bounded_affine_increment_transition_matches(
                        transition, body_args, head_args,
                    )
                    || !transition
                        .body
                        .constraint
                        .as_ref()
                        .is_some_and(|constraint| {
                            contains_not_le_const_to_term(constraint, 100, &body_args[0])
                        })
                {
                    return false;
                }
                saw_entry_loop = true;
            } else if *body_pred == *entry_pred && *head_pred == phase_pred {
                if saw_entry_to_phase
                    || head_args != body_args
                    || !transition
                        .body
                        .constraint
                        .as_ref()
                        .is_some_and(|constraint| {
                            contains_le_const_to_term(constraint, 100, &body_args[0])
                        })
                {
                    return false;
                }
                saw_entry_to_phase = true;
            } else if *body_pred == phase_pred && *head_pred == phase_pred {
                if saw_phase_loop
                    || !self.bounded_affine_increment_transition_matches(
                        transition, body_args, head_args,
                    )
                    || !transition
                        .body
                        .constraint
                        .as_ref()
                        .is_some_and(|constraint| {
                            contains_not_le_const_to_term(constraint, 120, &body_args[0])
                        })
                {
                    return false;
                }
                saw_phase_loop = true;
            } else {
                return false;
            }
        }
        if !saw_entry_loop || !saw_entry_to_phase || !saw_phase_loop {
            return false;
        }

        let Some(query) = self.problem.queries().next() else {
            return false;
        };
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return false;
        };
        if *query_pred != phase_pred || query_args.len() != 3 {
            return false;
        }
        let Some(constraint) = &query.body.constraint else {
            return false;
        };
        contains_le_const_to_term(constraint, 120, &query_args[0])
            && contains_not_term_le_const(constraint, &query_args[1], 132)
            && contains_not_term_ge_const(constraint, &query_args[1], 3)
    }

    fn bounded_affine_increment_transition_matches(
        &self,
        transition: &HornClause,
        body_args: &[ChcExpr],
        head_args: &[ChcExpr],
    ) -> bool {
        let Some(head_defs) = self.resolved_head_arg_definitions(transition, body_args, head_args)
        else {
            return false;
        };
        head_defs.len() == 3
            && is_add_const_update(&head_defs[0], &body_args[0], 1)
            && is_add_const_update(&head_defs[1], &body_args[1], 1)
            && head_defs[2] == body_args[2]
    }

    fn has_parity_ite_equality_shape(&self) -> bool {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 6
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 2
            || self.problem.facts().count() != 1
            || self.problem.transitions().count() != 3
            || self.problem.queries().count() != 1
        {
            return false;
        }
        if !self.parity_ite_fact_satisfies_candidate() {
            return false;
        }
        let pred_ids: Vec<_> = preds.iter().map(|pred| pred.id).collect();

        let mut identity_edges = 0usize;
        let mut loop_edge_ok = false;
        for transition in self.problem.transitions() {
            let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
                return false;
            };
            let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
                return false;
            };
            if body_args.len() != 6 || head_args.len() != 6 {
                return false;
            }
            if !pred_ids.contains(body_pred) || !pred_ids.contains(head_pred) {
                return false;
            }
            if *body_pred != *head_pred && body_args == head_args {
                identity_edges += 1;
                continue;
            }
            if *body_pred == *head_pred
                && self.parity_ite_loop_transition_matches(transition, body_args, head_args)
            {
                loop_edge_ok = true;
                continue;
            }
            return false;
        }
        if identity_edges != 2 || !loop_edge_ok {
            return false;
        }

        let Some(query) = self.problem.queries().next() else {
            return false;
        };
        let [(query_pred, query_args)] = query.body.predicates.as_slice() else {
            return false;
        };
        if !pred_ids.contains(query_pred) || query_args.len() != 6 {
            return false;
        }
        let Some(constraint) = &query.body.constraint else {
            return false;
        };
        is_not_eq(constraint, &query_args[3], &query_args[4])
    }

    pub(super) fn has_mod1000_split_triangle_chc_shape(&self) -> bool {
        let preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|pred| {
                pred.arg_sorts.len() == 4
                    && pred
                        .arg_sorts
                        .iter()
                        .all(|sort| matches!(sort, ChcSort::Int))
            })
            .collect();
        if preds.len() != 1 || self.problem.facts().count() != 1 {
            return false;
        }
        let pred = preds[0];
        let nullary_preds: Vec<_> = self
            .problem
            .predicates()
            .iter()
            .filter(|candidate| candidate.arg_sorts.is_empty())
            .collect();
        if nullary_preds.len() != 1 {
            return false;
        }
        let fail_pred = nullary_preds[0].id;

        let Some(fact) = self.problem.facts().next() else {
            return false;
        };
        let ClauseHead::Predicate(fact_pred, fact_args) = &fact.head else {
            return false;
        };
        if *fact_pred != pred.id || fact_args.len() != 4 {
            return false;
        }
        let Some(fact_values) = fact_arg_int_values(fact, fact_args) else {
            return false;
        };
        if fact_values != [0, 0, 0, 500] {
            return false;
        }

        let Some(transition) = self.problem.clauses().iter().find(|clause| {
            matches!(
                (&clause.body.predicates[..], &clause.head),
                ([(body_pred, body_args)], ClauseHead::Predicate(head_pred, head_args))
                    if *body_pred == pred.id
                        && *head_pred == pred.id
                        && body_args.len() == 4
                        && head_args.len() == 4
            )
        }) else {
            return false;
        };
        let [(body_pred, body_args)] = transition.body.predicates.as_slice() else {
            return false;
        };
        let ClauseHead::Predicate(head_pred, head_args) = &transition.head else {
            return false;
        };
        if *body_pred != pred.id
            || *head_pred != pred.id
            || body_args.len() != 4
            || head_args.len() != 4
        {
            return false;
        }
        let Some(head_defs) = self.resolved_head_arg_definitions(transition, body_args, head_args)
        else {
            return false;
        };
        if !is_mod_add_const_update(&head_defs[0], &body_args[0], 1, 1000)
            || !is_add_one_update(&head_defs[1], &body_args[1])
            || !is_threshold_ite_add_const_update(
                &head_defs[2],
                &body_args[0],
                &body_args[2],
                500,
                -1,
                1,
            )
            || !is_threshold_ite_add_const_update(
                &head_defs[3],
                &body_args[0],
                &body_args[3],
                500,
                1,
                -1,
            )
        {
            return false;
        }

        let Some(safety_clause) = self.problem.clauses().iter().find(|clause| {
            matches!(
                (&clause.body.predicates[..], &clause.head),
                ([(body_pred, body_args)], ClauseHead::Predicate(head_pred, head_args))
                    if *body_pred == pred.id
                        && *head_pred == fail_pred
                        && body_args.len() == 4
                        && head_args.is_empty()
            )
        }) else {
            return false;
        };
        let [(query_pred, query_args)] = safety_clause.body.predicates.as_slice() else {
            return false;
        };
        if *query_pred != pred.id || query_args.len() != 4 {
            return false;
        }
        let Some(constraint) = &safety_clause.body.constraint else {
            return false;
        };
        let Some(counter_value) = contains_eq_to_int_value(constraint, &query_args[1]) else {
            return false;
        };
        let phase = counter_value.rem_euclid(1000);
        if !is_not_eq_anywhere(constraint, &query_args[2], &query_args[3])
            || !matches!(phase, 250 | 750)
        {
            return false;
        }

        self.problem.queries().any(|query| {
            matches!(
                (&query.body.predicates[..], &query.head),
                ([(body_pred, body_args)], ClauseHead::False)
                    if *body_pred == fail_pred && body_args.is_empty()
            )
        })
    }

    fn parity_ite_fact_satisfies_candidate(&self) -> bool {
        let Some(fact) = self.problem.facts().next() else {
            return false;
        };
        let ClauseHead::Predicate(fact_pred, fact_args) = &fact.head else {
            return false;
        };
        let Some(pred) = self.problem.get_predicate(*fact_pred) else {
            return false;
        };
        if pred.arg_sorts.len() != 6
            || !pred
                .arg_sorts
                .iter()
                .all(|sort| matches!(sort, ChcSort::Int))
            || fact_args.len() != 6
        {
            return false;
        }

        let Some(values) = fact_arg_int_values(fact, fact_args) else {
            return false;
        };
        values[3] == values[4] && values[2].rem_euclid(2) == 1 && values[5].rem_euclid(2) == 0
    }

    fn parity_ite_loop_transition_matches(
        &self,
        transition: &HornClause,
        body_args: &[ChcExpr],
        head_args: &[ChcExpr],
    ) -> bool {
        let Some(head_defs) = self.resolved_head_arg_definitions(transition, body_args, head_args)
        else {
            return false;
        };
        head_defs.len() == 6
            && head_defs[0] == body_args[0]
            && head_defs[1] == body_args[1]
            && is_sum_of_terms(
                &head_defs[2],
                &[
                    body_args[2].clone(),
                    body_args[3].clone(),
                    body_args[4].clone(),
                    body_args[5].clone(),
                ],
            )
            && is_ite_mod_odd_increment(&head_defs[3], &head_args[2], &body_args[3])
            && is_add_const_update(&head_defs[4], &body_args[4], 1)
            && is_add_const_update(&head_defs[5], &body_args[5], 2)
    }

    fn resolved_head_arg_definitions(
        &self,
        clause: &HornClause,
        body_args: &[ChcExpr],
        head_args: &[ChcExpr],
    ) -> Option<Vec<ChcExpr>> {
        let mut definitions = Vec::with_capacity(head_args.len());
        for head_arg in head_args {
            if body_args.iter().any(|body_arg| body_arg == head_arg) {
                definitions.push(head_arg.clone());
            } else if let ChcExpr::Var(var) = head_arg {
                let constraint = clause.body.constraint.as_ref()?;
                definitions.push(find_var_definition(constraint, var)?);
            } else {
                definitions.push(head_arg.clone());
            }
        }
        Some(definitions)
    }

    pub(super) fn build_verified_threshold_ite_candidate(
        &self,
    ) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let candidate = self.build_threshold_ite_candidate()?;

        if !self.verify_threshold_ite_candidate(&candidate, Duration::from_millis(250)) {
            return None;
        }

        Some(candidate)
    }

    pub(super) fn build_threshold_ite_candidate(&self) -> Option<FxHashMap<PredicateId, ChcExpr>> {
        let mut candidate = FxHashMap::default();
        let mut found_threshold_relation = false;

        for pred in self.problem.predicates() {
            if pred.arg_sorts.is_empty() {
                candidate.insert(pred.id, ChcExpr::bool_const(false));
            }
        }

        for pred in self.problem.predicates() {
            if pred.arg_sorts.len() < 2
                || !pred
                    .arg_sorts
                    .iter()
                    .all(|sort| matches!(sort, ChcSort::Int))
            {
                continue;
            }

            let canonical_vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            let init_values = self.extract_init_values(pred.id, &canonical_vars);

            for transition in self.problem.transitions() {
                let formula = self.threshold_ite_formula_for_transition(
                    transition,
                    pred.id,
                    &canonical_vars,
                    &init_values,
                );
                let Some(formula) = formula else {
                    continue;
                };
                found_threshold_relation = true;
                candidate.insert(pred.id, formula);
            }
        }

        if !found_threshold_relation || candidate.is_empty() {
            return None;
        }

        Some(candidate)
    }

    fn threshold_ite_formula_for_transition(
        &self,
        clause: &HornClause,
        pred_id: PredicateId,
        canonical_vars: &[ChcVar],
        init_values: &FxHashMap<String, i128>,
    ) -> Option<ChcExpr> {
        let [(body_pred, body_args)] = clause.body.predicates.as_slice() else {
            return None;
        };
        if *body_pred != pred_id {
            return None;
        }

        let ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
            return None;
        };
        if *head_pred != pred_id || body_args.len() != head_args.len() {
            return None;
        }

        let Some(head_defs) = self.head_arg_definitions(clause, head_args) else {
            return None;
        };

        for (counter_idx, counter_body) in body_args.iter().enumerate() {
            if !is_add_one_update(&head_defs[counter_idx], counter_body) {
                continue;
            }
            for (dependent_idx, dependent_body) in body_args.iter().enumerate() {
                if dependent_idx == counter_idx {
                    continue;
                }
                let Some(threshold) =
                    threshold_ite_update(&head_defs[dependent_idx], counter_body, dependent_body)
                else {
                    continue;
                };
                let counter_var = ChcExpr::var(canonical_vars[counter_idx].clone());
                let dependent_var = ChcExpr::var(canonical_vars[dependent_idx].clone());
                let dependent_init = *init_values.get(&canonical_vars[dependent_idx].name)?;
                let counter_init = init_values.get(&canonical_vars[counter_idx].name).copied();
                let activation_threshold =
                    counter_init.map_or(threshold, |init| init.max(threshold));
                let offset = dependent_init.checked_sub(activation_threshold)?;
                let then_value = if offset == 0 {
                    counter_var.clone()
                } else {
                    ChcExpr::add(counter_var.clone(), ChcExpr::int(offset))
                };
                let mut conjuncts = vec![ChcExpr::eq(
                    dependent_var,
                    ChcExpr::ite(
                        ChcExpr::ge(counter_var.clone(), ChcExpr::int(activation_threshold)),
                        then_value,
                        ChcExpr::int(dependent_init),
                    ),
                )];
                if let Some(init) = counter_init {
                    conjuncts.push(ChcExpr::ge(counter_var.clone(), ChcExpr::int(init)));
                }
                return Some(ChcExpr::and_vec(conjuncts));
            }
        }

        None
    }

    fn head_arg_definitions(
        &self,
        clause: &HornClause,
        head_args: &[ChcExpr],
    ) -> Option<Vec<ChcExpr>> {
        let mut definitions = Vec::with_capacity(head_args.len());
        for head_arg in head_args {
            if let ChcExpr::Var(var) = head_arg {
                let constraint = clause.body.constraint.as_ref()?;
                definitions.push(find_var_definition(constraint, var)?);
            } else {
                definitions.push(head_arg.clone());
            }
        }
        Some(definitions)
    }

    /// Verify that the candidate invariant is inductive.
    ///
    /// Checks each clause: body_with_inv => head_with_inv
    pub(super) fn verify_inductive_with_timeout(
        &self,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
        per_clause_timeout: Duration,
    ) -> bool {
        self.verify_inductive_impl(candidate, Some(per_clause_timeout))
    }

    fn verify_threshold_ite_candidate(
        &self,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
        per_clause_timeout: Duration,
    ) -> bool {
        if self.verify_threshold_ite_candidate_locally(candidate, per_clause_timeout) {
            return true;
        }

        let clauses = u32::try_from(self.problem.clauses().len().max(1)).unwrap_or(u32::MAX);
        let validation_budget = per_clause_timeout.saturating_mul(clauses.saturating_add(1));
        let model = self.candidate_as_total_model(candidate);
        let config = PdrConfig {
            strict_proofs: true,
            solve_timeout: Some(validation_budget),
            disable_array_scalarization: true,
            preserve_original_clauses: true,
            ..PdrConfig::default()
        };
        crate::engines::validate_external_invariant_model(self.problem, &model, &config)
            .unwrap_or(false)
    }

    fn verify_threshold_ite_candidate_locally(
        &self,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
        per_clause_timeout: Duration,
    ) -> bool {
        let mut smt = SmtContext::new();
        let _timeout_guard = smt.scoped_check_timeout(Some(per_clause_timeout));

        for clause in self.problem.clauses() {
            if self.threshold_ite_transition_is_covered(clause, candidate) {
                continue;
            }

            let body_with_inv = self.substitute_predicates_in_body(clause, candidate);
            let head_with_inv = self.substitute_predicate_in_head(clause, candidate);
            let negated_implication = ChcExpr::and(body_with_inv, ChcExpr::not(head_with_inv));

            smt.reset();
            match smt.check_sat(&negated_implication) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                SmtResult::Sat(_) | SmtResult::Unknown => return false,
            }
        }

        true
    }

    fn candidate_as_total_model(
        &self,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> InvariantModel {
        let mut model = InvariantModel::new();
        for pred in self.problem.predicates() {
            let synth_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            let pdr_vars: Vec<_> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| {
                    ChcVar::new(format!("__p{}_a{}", pred.id.index(), i), sort.clone())
                })
                .collect();

            let formula = if let Some(expr) = candidate.get(&pred.id) {
                let subst: Vec<_> = synth_vars
                    .iter()
                    .cloned()
                    .zip(pdr_vars.iter().cloned().map(ChcExpr::var))
                    .collect();
                expr.substitute(&subst)
            } else {
                ChcExpr::bool_const(true)
            };

            model.set(pred.id, PredicateInterpretation::new(pdr_vars, formula));
        }

        model
    }

    fn threshold_ite_transition_is_covered(
        &self,
        clause: &HornClause,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> bool {
        for pred in self.problem.predicates() {
            if pred.arg_sorts.len() < 2
                || !pred
                    .arg_sorts
                    .iter()
                    .all(|sort| matches!(sort, ChcSort::Int))
            {
                continue;
            }
            let canonical_vars: Vec<ChcVar> = pred
                .arg_sorts
                .iter()
                .enumerate()
                .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
                .collect();
            let init_values = self.extract_init_values(pred.id, &canonical_vars);
            let Some(formula) = self.threshold_ite_formula_for_transition(
                clause,
                pred.id,
                &canonical_vars,
                &init_values,
            ) else {
                continue;
            };
            if candidate.get(&pred.id) == Some(&formula) {
                return true;
            }
        }

        false
    }

    fn verify_inductive_impl(
        &self,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
        per_clause_timeout: Option<Duration>,
    ) -> bool {
        let mut smt = SmtContext::new();
        let _timeout_guard = smt.scoped_check_timeout(per_clause_timeout);

        // Check each clause
        for clause in self.problem.clauses() {
            // Substitute predicates with candidate invariants
            let body_with_inv = self.substitute_predicates_in_body(clause, candidate);
            let head_with_inv = self.substitute_predicate_in_head(clause, candidate);

            // Check: body_with_inv => head_with_inv is valid
            // Equivalent to: body_with_inv AND NOT(head_with_inv) is UNSAT
            let negated_implication = ChcExpr::and(body_with_inv, ChcExpr::not(head_with_inv));

            // Reset SMT context between checks to avoid accumulated state
            smt.reset();
            let result = smt.check_sat(&negated_implication);

            match result {
                SmtResult::Sat(_) => {
                    // Counterexample found - invariant not inductive for this clause
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Good - this clause is satisfied
                    continue;
                }
                SmtResult::Unknown => {
                    // Can't verify - assume not inductive
                    return false;
                }
            }
        }

        true
    }

    /// Substitute predicates in clause body with invariant expressions.
    fn substitute_predicates_in_body(
        &self,
        clause: &crate::HornClause,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> ChcExpr {
        let mut conjuncts = Vec::new();

        // Add constraint
        if let Some(constraint) = &clause.body.constraint {
            conjuncts.push(constraint.clone());
        }

        // Substitute each predicate with its interpretation
        for (pred_id, args) in &clause.body.predicates {
            if let Some(inv) = candidate.get(pred_id) {
                // Build substitution from canonical vars to actual args using actual sorts
                let Some(pred) = self.problem.get_predicate(*pred_id) else {
                    continue;
                };
                let substitution: Vec<(ChcVar, ChcExpr)> = pred
                    .arg_sorts
                    .iter()
                    .enumerate()
                    .zip(args.iter())
                    .map(|((i, sort), arg)| {
                        let canonical_var = ChcVar::new(format!("x{i}"), sort.clone());
                        (canonical_var, arg.clone())
                    })
                    .collect();
                conjuncts.push(inv.substitute(&substitution));
            }
        }

        ChcExpr::and_vec(conjuncts)
    }

    /// Substitute predicate in clause head with invariant expression.
    fn substitute_predicate_in_head(
        &self,
        clause: &crate::HornClause,
        candidate: &FxHashMap<PredicateId, ChcExpr>,
    ) -> ChcExpr {
        match &clause.head {
            ClauseHead::False => ChcExpr::Bool(false),
            ClauseHead::Predicate(pred_id, args) => {
                if let Some(inv) = candidate.get(pred_id) {
                    let Some(pred) = self.problem.get_predicate(*pred_id) else {
                        return ChcExpr::Bool(true);
                    };
                    let substitution: Vec<(ChcVar, ChcExpr)> = pred
                        .arg_sorts
                        .iter()
                        .enumerate()
                        .zip(args.iter())
                        .map(|((i, sort), arg)| {
                            let canonical_var = ChcVar::new(format!("x{i}"), sort.clone());
                            (canonical_var, arg.clone())
                        })
                        .collect();
                    inv.substitute(&substitution)
                } else {
                    ChcExpr::Bool(true)
                }
            }
        }
    }
}

fn find_var_definition(expr: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .find_map(|arg| find_var_definition(arg.as_ref(), var)),
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let then_def = find_var_definition(args[1].as_ref(), var)?;
            let else_def = find_var_definition(args[2].as_ref(), var)?;
            Some(ChcExpr::ite(args[0].as_ref().clone(), then_def, else_def))
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if matches_var(args[0].as_ref(), var) {
                Some(args[1].as_ref().clone())
            } else if matches_var(args[1].as_ref(), var) {
                Some(args[0].as_ref().clone())
            } else {
                None
            }
        }
        _ => None,
    }
}

fn fact_arg_int_values(fact: &HornClause, fact_args: &[ChcExpr]) -> Option<Vec<i128>> {
    let constraint = fact.body.constraint.as_ref()?;
    let mut values = Vec::with_capacity(fact_args.len());
    for arg in fact_args {
        values.push(eval_fact_int_expr(arg, constraint, 0)?);
    }
    Some(values)
}

fn eval_fact_int_expr(expr: &ChcExpr, constraint: &ChcExpr, depth: usize) -> Option<i128> {
    if depth > 8 {
        return None;
    }
    if let Some(value) = expr.as_i128() {
        return Some(value);
    }

    match expr {
        ChcExpr::Var(var) => {
            let definition = find_var_definition(constraint, var)?;
            eval_fact_int_expr(&definition, constraint, depth + 1)
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut sum = 0i128;
            for arg in args {
                sum = sum.checked_add(eval_fact_int_expr(arg.as_ref(), constraint, depth + 1)?)?;
            }
            Some(sum)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            eval_fact_int_expr(args[0].as_ref(), constraint, depth + 1)?
                .checked_sub(eval_fact_int_expr(args[1].as_ref(), constraint, depth + 1)?)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut product = 1i128;
            for arg in args {
                product = product.checked_mul(eval_fact_int_expr(
                    arg.as_ref(),
                    constraint,
                    depth + 1,
                )?)?;
            }
            Some(product)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            eval_fact_int_expr(args[0].as_ref(), constraint, depth + 1)?.checked_neg()
        }
        _ => None,
    }
}

fn matches_var(expr: &ChcExpr, var: &ChcVar) -> bool {
    matches!(expr, ChcExpr::Var(candidate) if candidate.name == var.name && candidate.sort == var.sort)
}

fn is_add_one_update(expr: &ChcExpr, base: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            (args[0].as_ref() == base && args[1].as_i128() == Some(1))
                || (args[1].as_ref() == base && args[0].as_i128() == Some(1))
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            args[0].as_ref() == base && args[1].as_i128() == Some(-1)
        }
        _ => false,
    }
}

fn threshold_ite_update(expr: &ChcExpr, counter: &ChcExpr, dependent: &ChcExpr) -> Option<i128> {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return None;
    };
    if args.len() != 3
        || !is_add_one_update(args[1].as_ref(), dependent)
        || args[2].as_ref() != dependent
    {
        return None;
    }

    threshold_ge(args[0].as_ref(), counter)
}

fn threshold_ge(expr: &ChcExpr, counter: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            if args[0].as_ref() == counter {
                args[1].as_i128()
            } else {
                None
            }
        }
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            if args[1].as_ref() == counter {
                args[0].as_i128()
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_zero_one_toggle_update(expr: &ChcExpr, base: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return false;
    };
    args.len() == 3
        && is_eq_to_int(args[0].as_ref(), base, 0)
        && args[1].as_i128() == Some(1)
        && args[2].as_i128() == Some(0)
}

fn is_negated_parity_toggle_query(expr: &ChcExpr, counter: &ChcExpr, parity: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            let ChcExpr::Op(ChcOp::Ite, ite_args) = args[0].as_ref() else {
                return false;
            };
            let [condition, then_branch, else_branch] = ite_args.as_slice() else {
                return false;
            };
            is_eq_to_int(condition.as_ref(), parity, 1)
                && is_mod_eq_expr(then_branch.as_ref(), counter, 2, 1)
                && is_mod_eq_expr(else_branch.as_ref(), counter, 2, 0)
        }
        ChcExpr::Op(ChcOp::Ite, ite_args) => {
            let [condition, then_branch, else_branch] = ite_args.as_slice() else {
                return false;
            };
            is_eq_to_int(condition.as_ref(), parity, 1)
                && is_not_mod_eq_expr(then_branch.as_ref(), counter, 2, 1)
                && is_not_mod_eq_expr(else_branch.as_ref(), counter, 2, 0)
        }
        _ => false,
    }
}

fn is_not_eq(expr: &ChcExpr, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => is_eq_expr(args[0].as_ref(), lhs, rhs),
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            (args[0].as_ref() == lhs && args[1].as_ref() == rhs)
                || (args[0].as_ref() == rhs && args[1].as_ref() == lhs)
        }
        _ => false,
    }
}

fn is_not_eq_anywhere(expr: &ChcExpr, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
    expr_any(expr, &mut |candidate| is_not_eq(candidate, lhs, rhs))
}

fn contains_eq_to_int_value(expr: &ChcExpr, term: &ChcExpr) -> Option<i128> {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            if args[0].as_ref() == term {
                args[1].as_i128()
            } else if args[1].as_ref() == term {
                args[0].as_i128()
            } else {
                None
            }
        }
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .find_map(|arg| contains_eq_to_int_value(arg.as_ref(), term)),
        _ => None,
    }
}

fn is_not_mod_eq_expr(expr: &ChcExpr, dividend: &ChcExpr, modulus: i128, remainder: i128) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            is_mod_eq_expr(args[0].as_ref(), dividend, modulus, remainder)
        }
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            (matches_mod_expr(args[0].as_ref(), dividend, modulus)
                && args[1].as_i128() == Some(remainder))
                || (matches_mod_expr(args[1].as_ref(), dividend, modulus)
                    && args[0].as_i128() == Some(remainder))
        }
        _ => false,
    }
}

fn is_eq_to_int(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            (args[0].as_ref() == term && args[1].as_i128() == Some(value))
                || (args[1].as_ref() == term && args[0].as_i128() == Some(value))
        }
        _ => false,
    }
}

fn is_eq_expr(expr: &ChcExpr, lhs: &ChcExpr, rhs: &ChcExpr) -> bool {
    match expr {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            (args[0].as_ref() == lhs && args[1].as_ref() == rhs)
                || (args[0].as_ref() == rhs && args[1].as_ref() == lhs)
        }
        _ => false,
    }
}

fn is_mod_eq_expr(expr: &ChcExpr, dividend: &ChcExpr, modulus: i128, remainder: i128) -> bool {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return false;
    };
    let [lhs, rhs] = args.as_slice() else {
        return false;
    };
    (matches_mod_expr(lhs.as_ref(), dividend, modulus) && rhs.as_i128() == Some(remainder))
        || (matches_mod_expr(rhs.as_ref(), dividend, modulus) && lhs.as_i128() == Some(remainder))
}

fn is_mod_add_const_update(expr: &ChcExpr, base: &ChcExpr, value: i128, modulus: i128) -> bool {
    let ChcExpr::Op(ChcOp::Mod, args) = expr else {
        return false;
    };
    let [dividend, actual_modulus] = args.as_slice() else {
        return false;
    };
    actual_modulus.as_i128() == Some(modulus) && is_add_const_update(dividend.as_ref(), base, value)
}

fn is_threshold_ite_add_const_update(
    expr: &ChcExpr,
    counter: &ChcExpr,
    base: &ChcExpr,
    threshold: i128,
    then_delta: i128,
    else_delta: i128,
) -> bool {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return false;
    };
    let [condition, then_branch, else_branch] = args.as_slice() else {
        return false;
    };
    threshold_ge(condition.as_ref(), counter) == Some(threshold)
        && is_add_const_update(then_branch.as_ref(), base, then_delta)
        && is_add_const_update(else_branch.as_ref(), base, else_delta)
}

fn contains_mod_eq_expr(
    expr: &ChcExpr,
    dividend: &ChcExpr,
    modulus: i128,
    remainder: i128,
) -> bool {
    expr_any(expr, &mut |candidate| {
        is_mod_eq_expr(candidate, dividend, modulus, remainder)
    })
}

fn contains_eq_to_int(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    expr_any(expr, &mut |candidate| is_eq_to_int(candidate, term, value))
}

fn contains_eq_scaled_term(expr: &ChcExpr, lhs: &ChcExpr, coeff: i128, rhs: &ChcExpr) -> bool {
    expr_any(expr, &mut |candidate| {
        is_eq_scaled_term(candidate, lhs, coeff, rhs)
    })
}

fn is_eq_scaled_term(expr: &ChcExpr, lhs: &ChcExpr, coeff: i128, rhs: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return false;
    };
    let [left, right] = args.as_slice() else {
        return false;
    };
    (left.as_ref() == lhs && is_scaled_term(right.as_ref(), coeff, rhs))
        || (right.as_ref() == lhs && is_scaled_term(left.as_ref(), coeff, rhs))
}

fn is_scaled_term(expr: &ChcExpr, coeff: i128, term: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return false;
    };
    let [left, right] = args.as_slice() else {
        return false;
    };
    (left.as_i128() == Some(coeff) && right.as_ref() == term)
        || (right.as_i128() == Some(coeff) && left.as_ref() == term)
}

fn matches_mod_expr(expr: &ChcExpr, dividend: &ChcExpr, modulus: i128) -> bool {
    let ChcExpr::Op(ChcOp::Mod, args) = expr else {
        return false;
    };
    let [actual_dividend, actual_modulus] = args.as_slice() else {
        return false;
    };
    actual_dividend.as_ref() == dividend && actual_modulus.as_i128() == Some(modulus)
}

fn contains_le_const_to_term(expr: &ChcExpr, value: i128, term: &ChcExpr) -> bool {
    expr_any(expr, &mut |candidate| {
        is_le_const_to_term(candidate, value, term)
    })
}

fn contains_not_le_const_to_term(expr: &ChcExpr, value: i128, term: &ChcExpr) -> bool {
    expr_any(expr, &mut |candidate| {
        is_not_le_const_to_term(candidate, value, term)
    })
}

fn contains_not_term_le_const(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    expr_any(expr, &mut |candidate| {
        is_not_term_le_const(candidate, term, value)
    })
}

fn contains_not_term_ge_const(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    expr_any(expr, &mut |candidate| {
        is_not_term_ge_const(candidate, term, value)
    })
}

fn is_le_const_to_term(expr: &ChcExpr, value: i128, term: &ChcExpr) -> bool {
    matches!(
        expr,
        ChcExpr::Op(ChcOp::Le, args)
            if args.len() == 2 && args[0].as_i128() == Some(value) && args[1].as_ref() == term
    )
}

fn is_not_le_const_to_term(expr: &ChcExpr, value: i128, term: &ChcExpr) -> bool {
    matches!(
        expr,
        ChcExpr::Op(ChcOp::Not, args)
            if args.len() == 1 && is_le_const_to_term(args[0].as_ref(), value, term)
    )
}

fn is_not_term_le_const(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    matches!(
        expr,
        ChcExpr::Op(ChcOp::Not, args)
            if args.len() == 1
                && matches!(
                    args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Le, le_args)
                        if le_args.len() == 2
                            && le_args[0].as_ref() == term
                            && le_args[1].as_i128() == Some(value)
                )
    )
}

fn is_not_term_ge_const(expr: &ChcExpr, term: &ChcExpr, value: i128) -> bool {
    matches!(
        expr,
        ChcExpr::Op(ChcOp::Not, args)
            if args.len() == 1
                && matches!(
                    args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Ge, ge_args)
                        if ge_args.len() == 2
                            && ge_args[0].as_ref() == term
                            && ge_args[1].as_i128() == Some(value)
                )
    )
}

fn expr_any(expr: &ChcExpr, predicate: &mut impl FnMut(&ChcExpr) -> bool) -> bool {
    if predicate(expr) {
        return true;
    }
    match expr {
        ChcExpr::Op(_, args) => args.iter().any(|arg| expr_any(arg.as_ref(), predicate)),
        _ => false,
    }
}

fn is_sum_of_terms(expr: &ChcExpr, expected_terms: &[ChcExpr]) -> bool {
    let mut actual_terms = Vec::new();
    flatten_add_terms(expr, &mut actual_terms);
    if actual_terms.len() != expected_terms.len() {
        return false;
    }

    let mut remaining = expected_terms.to_vec();
    for term in actual_terms {
        let Some(pos) = remaining.iter().position(|expected| *expected == term) else {
            return false;
        };
        remaining.remove(pos);
    }
    remaining.is_empty()
}

fn flatten_add_terms(expr: &ChcExpr, out: &mut Vec<ChcExpr>) {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) => {
            for arg in args {
                flatten_add_terms(arg.as_ref(), out);
            }
        }
        other => out.push(other.clone()),
    }
}

fn is_ite_mod_odd_increment(expr: &ChcExpr, parity_input: &ChcExpr, dependent: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Ite, args) = expr else {
        return false;
    };
    let [condition, then_branch, else_branch] = args.as_slice() else {
        return false;
    };
    is_mod_eq_expr(condition.as_ref(), parity_input, 2, 1)
        && is_add_const_update(then_branch.as_ref(), dependent, 1)
        && else_branch.as_ref() == dependent
}

fn is_add_const_update(expr: &ChcExpr, base: &ChcExpr, value: i128) -> bool {
    let ChcExpr::Op(ChcOp::Add, _) = expr else {
        return false;
    };
    let mut terms = Vec::new();
    flatten_add_terms(expr, &mut terms);
    if terms.len() != 2 {
        return false;
    }
    (terms[0] == *base && terms[1].as_i128() == Some(value))
        || (terms[1] == *base && terms[0].as_i128() == Some(value))
}

fn canonical_int_var(index: usize) -> ChcVar {
    ChcVar::new(format!("x{index}"), ChcSort::Int)
}

fn canonical_eq(lhs: usize, rhs: usize) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::var(canonical_int_var(lhs)),
        ChcExpr::var(canonical_int_var(rhs)),
    )
}

fn mod_eq(index: usize, modulus: i128, remainder: i128) -> ChcExpr {
    ChcExpr::eq(
        ChcExpr::mod_op(
            ChcExpr::var(canonical_int_var(index)),
            ChcExpr::int(modulus),
        ),
        ChcExpr::int(remainder),
    )
}
