// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Multi-definition inlining phase (Z3-style eager inlining).
//!
//! Identifies predicates with multiple defining clauses and few tail uses,
//! then expands each use site into N clauses (one per definition).
//!
//! Reference: Z3 `dl_mk_rule_inliner.cpp:plan_inlining()` + `transform_rules()`.

use super::ClauseInliner;
use crate::{ChcExpr, ClauseBody, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Hard cap on definition count in graph-collapse mode. Golem's
/// `SimpleNodeEliminator` is unbounded; we keep a generous bound so a
/// pathological N-in/1-out join cannot expand into thousands of clauses.
const GRAPH_COLLAPSE_MAX_DEFS: usize = 64;

impl ClauseInliner {
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
    ) -> (Vec<HornClause>, bool) {
        // Count head occurrences (definitions) and tail occurrences per predicate.
        let mut head_count: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut tail_count: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut def_indices: FxHashMap<PredicateId, Vec<usize>> = FxHashMap::default();
        let mut is_self_recursive: FxHashSet<PredicateId> = FxHashSet::default();

        for (idx, clause) in clauses.iter().enumerate() {
            if let Some(head_id) = clause.head.predicate_id() {
                *head_count.entry(head_id).or_insert(0) += 1;
                def_indices.entry(head_id).or_default().push(idx);

                // Check self-recursion
                if clause.body.predicates.iter().any(|(id, _)| *id == head_id) {
                    is_self_recursive.insert(head_id);
                }
            }
            for (body_pred, _) in &clause.body.predicates {
                *tail_count.entry(*body_pred).or_insert(0) += 1;
            }
        }

        // Identify candidate predicates for multi-def inlining.
        let mut candidates: FxHashSet<PredicateId> = FxHashSet::default();
        let query_body_preds = if self.preserve_query_body_predicates {
            Self::query_body_predicates(clauses)
        } else {
            FxHashSet::default()
        };
        for (&pred, &h_count) in &head_count {
            if h_count < 2 {
                continue;
            }
            if query_body_preds.contains(&pred) {
                continue;
            }
            let t_count = tail_count.get(&pred).copied().unwrap_or(0);
            if self.graph_collapse_node_rule {
                // Golem's SimpleNodeEliminator rule (NodeEliminator.cc):
                // contract an internal vertex when |in|*|out| <= |in|+|out|,
                // i.e. the def×use cross product never grows the clause
                // count (N-in/1-out joins, 2-in/2-out diamonds; 1-in is
                // already handled by unique-definition phase 1).
                if h_count > GRAPH_COLLAPSE_MAX_DEFS {
                    continue;
                }
                if h_count.saturating_mul(t_count) > h_count + t_count {
                    continue;
                }
                // Mirror golem's linear-edge restriction: vertex contraction
                // only composes simple (non-hyper) in/out edges. Requiring
                // single-occurrence linear use clauses also guarantees the
                // one-level expansion below replaces EVERY occurrence of the
                // candidate.
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
            } else {
                if h_count > self.max_multi_defs {
                    continue;
                }
                if t_count > self.max_multi_tail_uses {
                    continue;
                }
            }
            if is_self_recursive.contains(&pred) {
                continue;
            }
            // Check constraint sizes of all definitions
            let all_within_limit = def_indices[&pred].iter().all(|&idx| {
                let constraint_size = clauses[idx]
                    .body
                    .constraint
                    .as_ref()
                    .map_or(0, Self::expr_size);
                constraint_size <= self.constraint_size_limit
            });
            if !all_within_limit {
                continue;
            }
            candidates.insert(pred);
        }

        if candidates.is_empty() {
            return (clauses.to_vec(), false);
        }

        // Z3 multiplier prevention: don't inline two multi-def predicates in
        // the same clause body (cross-product blowup). For each clause, check
        // how many candidate predicates appear in its body. If >1, forbid all
        // but the one with the fewest definitions to limit expansion.
        let mut forbidden: FxHashSet<PredicateId> = FxHashSet::default();
        for clause in clauses {
            let body_candidates: Vec<PredicateId> = clause
                .body
                .predicates
                .iter()
                .filter_map(|(id, _)| {
                    if candidates.contains(id) && !forbidden.contains(id) {
                        Some(*id)
                    } else {
                        None
                    }
                })
                .collect();
            if body_candidates.len() > 1 {
                // Keep the one with fewest definitions, forbid the rest
                let mut sorted = body_candidates;
                sorted.sort_by_key(|p| head_count.get(p).copied().unwrap_or(0));
                // Forbid all except the first (fewest definitions)
                for &p in &sorted[1..] {
                    forbidden.insert(p);
                }
            }
        }
        for p in &forbidden {
            candidates.remove(p);
        }

        // #9604: This pass removes every selected candidate definition before
        // expanding use sites. Since expansion is intentionally one-level, a
        // selected definition must not introduce another selected predicate in
        // its body; otherwise the introduced predicate has had all of its
        // definitions removed and the transformed problem is underconstrained.
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
        for pred in &dependency_forbidden {
            candidates.remove(pred);
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
        let multi_defs: FxHashMap<PredicateId, Vec<HornClause>> = candidates
            .iter()
            .map(|&pred| {
                let defs: Vec<HornClause> = def_indices[&pred]
                    .iter()
                    .map(|&idx| clauses[idx].clone())
                    .collect();
                (pred, defs)
            })
            .collect();

        // Record inlined definitions for back-translation. For multi-def
        // predicates, we create a disjunctive interpretation: the predicate
        // is true iff ANY of its defining clauses' bodies are satisfied.
        for (&pred_id, defs) in &multi_defs {
            for def in defs {
                let normalized = Self::normalize_head_for_back_translation(def);
                inlined_defs.push((pred_id, normalized));
            }
        }

        // Perform expansion: for each clause NOT defining a candidate, if its
        // body contains a candidate predicate, expand into N clauses.
        let candidate_heads: FxHashSet<PredicateId> = candidates.clone();
        let mut result: Vec<HornClause> = Vec::new();

        for clause in clauses {
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

                for def_clause in defs {
                    // Multi-def expansion drops the composition traces wholesale
                    // (the clause list is rewritten), so the linking definitions
                    // have nothing to attach to here.
                    let inlined = self.inline_clause(def_clause, call_args);
                    let (inlined_preds, inlined_constraint) =
                        (inlined.body_preds, inlined.constraint);

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

                    result.push(HornClause::new(
                        ClauseBody::new(new_body_preds, final_constraint),
                        clause.head.clone(),
                    ));
                }
            } else {
                // No multi-def predicate in body — keep as-is
                result.push(clause.clone());
            }
        }

        if self.verbose {
            safe_eprintln!(
                "CHC multi-def inlining: {} clauses → {} clauses, eliminated {} predicates",
                clauses.len(),
                result.len(),
                candidates.len()
            );
        }

        // Run unique-def inlining again in case multi-def expansion exposed
        // new unique-definition predicates. This is a light fixpoint.
        // We don't recurse multi-def again to prevent exponential blowup.
        let mut iteration = 0;
        loop {
            iteration += 1;
            let unique_def_indices = self.find_unique_def_indices(&result);
            if unique_def_indices.is_empty() {
                break;
            }
            let final_def_indices = self.extract_acyclic_def_indices(&result, unique_def_indices);
            if final_def_indices.is_empty() {
                break;
            }
            let final_defs: FxHashMap<PredicateId, HornClause> = final_def_indices
                .iter()
                .map(|(&pred_id, &clause_idx)| (pred_id, result[clause_idx].clone()))
                .collect();

            if self.verbose {
                safe_eprintln!(
                    "CHC multi-def post-cleanup iteration {}: inlining {} more predicates",
                    iteration,
                    final_defs.len()
                );
            }

            for (&pred_id, clause) in &final_defs {
                let normalized = Self::normalize_head_for_back_translation(clause);
                inlined_defs.push((pred_id, normalized));
            }

            let inlined_heads: FxHashSet<PredicateId> = final_defs.keys().copied().collect();
            result.retain(|c| {
                if let Some(head_id) = c.head.predicate_id() {
                    !inlined_heads.contains(&head_id)
                } else {
                    true
                }
            });
            result = result
                .into_iter()
                .map(|c| self.apply_defs(&c, &final_defs))
                .collect();
        }

        (result, true)
    }
}
