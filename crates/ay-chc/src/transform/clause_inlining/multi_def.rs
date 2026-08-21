// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Multi-definition inlining phase (Z3-style eager inlining).
//!
//! Identifies predicates with multiple defining clauses and few tail uses,
//! then expands each use site into N clauses (one per definition).
//!
//! Reference: Z3 `dl_mk_rule_inliner.cpp:plan_inlining()` + `transform_rules()`.

use super::{ClauseInliner, ClauseTrace, CompositionStep};
use crate::{ChcExpr, ClauseBody, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Hard cap on definition count in graph-collapse mode. Golem's
/// `SimpleNodeEliminator` is unbounded; we keep a generous bound so a
/// pathological N-in/1-out join cannot expand into thousands of clauses.
const GRAPH_COLLAPSE_MAX_DEFS: usize = 64;

struct MultiDefPlan {
    candidates: FxHashSet<PredicateId>,
    head_count: FxHashMap<PredicateId, usize>,
    tail_count: FxHashMap<PredicateId, usize>,
    def_indices: FxHashMap<PredicateId, Vec<usize>>,
}

impl ClauseInliner {
    /// Compute the exact phase-2 candidate set before trace-shape filtering.
    ///
    /// Phase 1 uses this same plan to preserve only the immediate neighbours
    /// that phase 2 can actually contract. Sharing the planner prevents a
    /// conservative "all multi-defined predicates" approximation from
    /// blocking unrelated unique-definition collapse.
    fn plan_multi_def(&self, clauses: &[HornClause]) -> MultiDefPlan {
        let mut head_count: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut tail_count: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut def_indices: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
        let mut is_self_recursive: FxHashSet<PredicateId> = FxHashSet::default();

        for (idx, clause) in clauses.iter().enumerate() {
            if let Some(head_id) = clause.head.predicate_id() {
                *head_count.entry(head_id).or_insert(0) += 1;
                def_indices.entry(head_id).or_default().push(idx);
                if clause.body.predicates.iter().any(|(id, _)| *id == head_id) {
                    is_self_recursive.insert(head_id);
                }
            }
            for (body_pred, _) in &clause.body.predicates {
                *tail_count.entry(*body_pred).or_insert(0) += 1;
            }
        }

        let mut candidates: FxHashSet<PredicateId> = FxHashSet::default();
        let query_body_preds = if self.preserve_query_body_predicates {
            Self::query_body_predicates(clauses)
        } else {
            FxHashSet::default()
        };
        for (&pred, &h_count) in &head_count {
            if h_count < 2 || query_body_preds.contains(&pred) {
                continue;
            }
            let t_count = tail_count.get(&pred).copied().unwrap_or(0);
            if self.graph_collapse_node_rule {
                if h_count > GRAPH_COLLAPSE_MAX_DEFS
                    || h_count.saturating_mul(t_count) > h_count + t_count
                {
                    continue;
                }
                let defs_linear = def_indices[&pred]
                    .iter()
                    .all(|&idx| clauses[idx].body.predicates.len() <= 1);
                if !defs_linear {
                    continue;
                }
                let uses_linear = clauses.iter().all(|clause| {
                    let occurrences = clause
                        .body
                        .predicates
                        .iter()
                        .filter(|(id, _)| *id == pred)
                        .count();
                    occurrences == 0 || (occurrences == 1 && clause.body.predicates.len() == 1)
                });
                if !uses_linear {
                    continue;
                }
            } else if h_count > self.max_multi_defs || t_count > self.max_multi_tail_uses {
                continue;
            }
            if is_self_recursive.contains(&pred) {
                continue;
            }
            let all_within_limit = def_indices[&pred].iter().all(|&idx| {
                clauses[idx]
                    .body
                    .constraint
                    .as_ref()
                    .map_or(0, Self::expr_size)
                    <= self.constraint_size_limit
            });
            if all_within_limit {
                candidates.insert(pred);
            }
        }

        // Avoid cross-product expansion when multiple selected predicates
        // occur in one clause.
        let mut forbidden: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in clauses {
            let body_candidates: Vec<PredicateId> = clause
                .body
                .predicates
                .iter()
                .filter_map(|(id, _)| {
                    (candidates.contains(id) && !forbidden.contains(id)).then_some(*id)
                })
                .collect();
            if body_candidates.len() > 1 {
                let mut sorted = body_candidates;
                sorted.sort_by_key(|pred| head_count.get(pred).copied().unwrap_or(0));
                forbidden.extend(sorted[1..].iter().copied());
            }
        }
        candidates.retain(|pred| !forbidden.contains(pred));

        // A one-level rewrite may not remove a selected predicate whose
        // definition introduces another selected predicate: the selected set
        // must be "def-independent". The default path enforces this by dropping
        // BOTH endpoints of every offending edge — simple, but it refuses to
        // break a mutual-recursion 2-cycle (P0's def references P1 and P1's def
        // references P0), which is exactly the shape a contracted loop SCC
        // (header <-> body block) reduces to, and a multi-predicate cyclic
        // shape PDR cannot discharge.
        //
        // #loop-scc-linearization (graph-collapse mode only): drop exactly ONE
        // endpoint per offending edge. The dropped predicate stays as an
        // ordinary predicate; the other is eliminated by one-level resolution
        // against its uses, closing a 2-cycle into a single SELF-recursive
        // predicate — the shape the IC3 lane / PDR already prove. Sound because
        // it is still one-level substitution (the eliminated predicate's def now
        // references only non-selected predicates), and the graph-collapse
        // back-translator re-validates every Safe model and replays every
        // Unsafe witness against the ORIGINAL clauses, so an over-eager
        // elimination can never turn a refuted obligation safe
        // (`node_eliminator::tests::linearizes_mutual_recursion_cycle_*`).
        if self.graph_collapse_node_rule {
            // Iteratively remove one endpoint (deterministically the
            // larger-index predicate) of the first offending edge in index
            // order until the selected set is def-independent; the outer
            // NodeEliminator loop then peels one block-predicate per round.
            loop {
                let mut sorted: Vec<PredicateId> = candidates.iter().copied().collect();
                sorted.sort_unstable_by_key(|p| p.index());
                let offending = sorted.iter().find_map(|&pred| {
                    def_indices[&pred].iter().find_map(|&idx| {
                        clauses[idx]
                            .body
                            .predicates
                            .iter()
                            .find_map(|(body_pred, _)| {
                                (*body_pred != pred && candidates.contains(body_pred)).then(|| {
                                    if pred.index() >= body_pred.index() {
                                        pred
                                    } else {
                                        *body_pred
                                    }
                                })
                            })
                    })
                });
                match offending {
                    Some(drop) => {
                        candidates.remove(&drop);
                    }
                    None => break,
                }
            }
        } else {
            let mut dependency_forbidden: FxHashSet<PredicateId> = FxHashSet::default();
            for &pred in &candidates {
                for &idx in &def_indices[&pred] {
                    for (body_pred, _) in &clauses[idx].body.predicates {
                        if candidates.contains(body_pred) {
                            dependency_forbidden.insert(pred);
                            dependency_forbidden.insert(*body_pred);
                        }
                    }
                }
            }
            candidates.retain(|pred| !dependency_forbidden.contains(pred));
        }

        MultiDefPlan {
            candidates,
            head_count,
            tail_count,
            def_indices,
        }
    }

    pub(super) fn multi_def_candidates(&self, clauses: &[HornClause]) -> FxHashSet<PredicateId> {
        self.plan_multi_def(clauses).candidates
    }

    /// Multi-definition inlining phase (Z3-style eager inlining).
    ///
    /// Identifies predicates P with:
    /// - 2..=max_multi_defs defining clauses (multiple definitions)
    /// - ≤max_multi_tail_uses tail occurrences across all clauses
    /// - No self-recursive definitions
    /// - No negative occurrences (not in CHC, so this is trivially satisfied)
    ///
    /// For each such predicate P, every clause containing P(args) in its body
    /// is expanded into N clauses (one per definition of P), with P's body
    /// substituted in. The original clause and P's defining clauses are removed.
    /// The Boolean result records whether that index-invalidating rewrite ran;
    /// clause-count equality is not sufficient to infer it.
    ///
    /// Reference: Z3 `dl_mk_rule_inliner.cpp:plan_inlining()` + `transform_rules()`.
    pub(super) fn inline_multi_def(
        &self,
        clauses: &[HornClause],
        inlined_defs: &mut Vec<(PredicateId, HornClause)>,
        traces: &mut Vec<ClauseTrace>,
    ) -> (Vec<HornClause>, bool) {
        let MultiDefPlan {
            mut candidates,
            head_count,
            tail_count,
            def_indices,
        } = self.plan_multi_def(clauses);

        if crate::ground_derivation::ground_backtranslation_enabled() {
            // The current trace format represents one composition layer. A
            // multi-def expansion has exact source correspondence only when
            // both its selected definition and every caller are still
            // uncomposed. Keep any nested case explicit rather than discarding
            // alignment for the entire inliner.
            candidates.retain(|pred| {
                def_indices[pred]
                    .iter()
                    .all(|index| traces.get(*index).is_some_and(ClauseTrace::is_uncomposed))
                    && clauses.iter().enumerate().all(|(index, clause)| {
                        let calls_pred = clause
                            .body
                            .predicates
                            .iter()
                            .any(|(body_pred, _)| body_pred == pred);
                        !calls_pred || traces.get(index).is_some_and(ClauseTrace::is_uncomposed)
                    })
            });
        }

        if candidates.is_empty() {
            return (clauses.to_vec(), false);
        }

        if self.verbose {
            let candidate_info: Vec<_> = candidates
                .iter()
                .map(|p| {
                    format!(
                        "P{}({}defs,{}tails)",
                        p.0,
                        head_count[p],
                        tail_count.get(p).copied().unwrap_or(0)
                    )
                })
                .collect();
            safe_eprintln!(
                "CHC multi-def inlining: {} candidates: {:?}",
                candidates.len(),
                candidate_info
            );
        }

        // Build the multi-definition map: predicate → list of defining clauses.
        let multi_defs: FxHashMap<PredicateId, Vec<(usize, HornClause)>> = candidates
            .iter()
            .map(|&pred| {
                let defs: Vec<(usize, HornClause)> = def_indices[&pred]
                    .iter()
                    .map(|&idx| (idx, clauses[idx].clone()))
                    .collect();
                (pred, defs)
            })
            .collect();

        // Record inlined definitions for back-translation. For multi-def
        // predicates, we create a disjunctive interpretation: the predicate
        // is true iff ANY of its defining clauses' bodies are satisfied.
        for (&pred_id, defs) in &multi_defs {
            for (_, def) in defs {
                let normalized = Self::normalize_head_for_back_translation(def);
                inlined_defs.push((pred_id, normalized));
            }
        }

        // Perform expansion: for each clause NOT defining a candidate, if its
        // body contains a candidate predicate, expand into N clauses.
        let candidate_heads: FxHashSet<PredicateId> = candidates.clone();
        let mut result: Vec<HornClause> = Vec::new();
        let track_ground = crate::ground_derivation::ground_backtranslation_enabled();
        let mut result_traces: Vec<ClauseTrace> = Vec::new();

        for (clause_index, clause) in clauses.iter().enumerate() {
            // Skip defining clauses of candidate predicates
            if let Some(head_id) = clause.head.predicate_id() {
                if candidate_heads.contains(&head_id) {
                    continue;
                }
            }

            // Check if any body predicate is a candidate
            let multi_def_in_body: Option<(usize, PredicateId)> = clause
                .body
                .predicates
                .iter()
                .enumerate()
                .find_map(|(i, (id, _))| {
                    if candidates.contains(id) {
                        Some((i, *id))
                    } else {
                        None
                    }
                });

            if let Some((body_idx, pred_id)) = multi_def_in_body {
                // Expand: create one clause per definition of pred_id
                let defs = &multi_defs[&pred_id];
                let call_args = &clause.body.predicates[body_idx].1;

                for (def_index, def_clause) in defs {
                    let inlined = self.inline_clause(def_clause, call_args);
                    let inlined_preds = inlined.body_preds.clone();
                    let inlined_constraint = inlined.constraint.clone();

                    // Build new body: replace the inlined predicate with its body preds
                    let mut new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
                    for (i, (id, args)) in clause.body.predicates.iter().enumerate() {
                        if i == body_idx {
                            // Replace with inlined body preds
                            new_body_preds.extend(inlined_preds.clone());
                        } else {
                            new_body_preds.push((*id, args.clone()));
                        }
                    }

                    // Combine constraints
                    let mut constraints: Vec<ChcExpr> = Vec::new();
                    if let Some(c) = &clause.body.constraint {
                        constraints.push(c.clone());
                    }
                    if let Some(c) = inlined_constraint {
                        constraints.push(c);
                    }
                    let final_constraint = if constraints.is_empty() {
                        None
                    } else {
                        Some(
                            constraints
                                .into_iter()
                                .reduce(ChcExpr::and)
                                .expect("non-empty"),
                        )
                    };

                    let expanded_clause = HornClause::new(
                        ClauseBody::new(new_body_preds, final_constraint),
                        clause.head.clone(),
                    );
                    if track_ground {
                        let mut trace = traces[clause_index].clone();
                        trace.original_clause = Some(clause.clone());
                        trace.composite_clause = Some(expanded_clause.clone());
                        trace.steps.insert(
                            pred_id,
                            CompositionStep {
                                inlined_pred: pred_id,
                                call_args: call_args.clone(),
                                def_clause: def_clause.clone(),
                                def_input_index: Some(traces[*def_index].c0_input_index),
                                linking_defs: inlined.linking_defs,
                                var_renames: inlined.var_renames,
                            },
                        );
                        result_traces.push(trace);
                    }
                    result.push(expanded_clause);
                }
            } else {
                // No multi-def predicate in body — keep as-is
                result.push(clause.clone());
                if track_ground {
                    result_traces.push(traces[clause_index].clone());
                }
            }
        }
        if track_ground {
            *traces = result_traces;
        }

        if self.verbose {
            safe_eprintln!(
                "CHC multi-def inlining: {} clauses → {} clauses, eliminated {} predicates",
                clauses.len(),
                result.len(),
                candidates.len()
            );
        }

        (result, true)
    }
}
