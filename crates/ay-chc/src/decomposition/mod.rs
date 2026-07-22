// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof decomposition for multi-predicate CHC problems.
//!
//! Multi-predicate CHC problems are exponentially harder when predicates interact.
//! This module implements proof decomposition to solve predicates in topological
//! order, substituting known invariants into subsequent subproblems.
//!
//! # Algorithm
//!
//! 1. Build predicate dependency graph from clause structure
//! 2. Find strongly connected components (SCCs) using Tarjan's algorithm
//! 3. Topologically sort SCCs
//! 4. For each SCC in order:
//!    - Extract subproblem containing only relevant predicates
//!    - Substitute known invariants from solved predicates
//!    - Solve the subproblem
//!    - Record the invariant
//!
//! # Decomposition Cases
//!
//! | Graph Structure | Strategy | Benefit |
//! |-----------------|----------|---------|
//! | Linear chain: P1→P2→P3 | Solve forward | Each step simpler |
//! | Tree: P1→{P2,P3} | Solve root first | Children independent |
//! | DAG with weak edges | Cut at weak edges | Smaller components |
//! | Strongly connected | No decomposition | Must solve jointly |
//!
//! # References
//!
//! - Issue #1871: CHC proof decomposition for multi-predicate problems
//! - the development design notes (Phase 5a)

use crate::engine_config::ChcEngineConfig;
use crate::pdr::scc::{tarjan_scc, PredicateSCC, SCCInfo};
use crate::pdr::{InvariantModel, PdrConfig, PdrResult, PdrSolver, PredicateInterpretation};
use crate::{ChcExpr, ChcProblem, ChcVar, ClauseBody, ClauseHead, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
mod tests;

/// Result of proof decomposition (type alias for unified ChcEngineResult).
pub(crate) type DecompositionResult = crate::engine_result::ChcEngineResult;

/// Configuration for decomposition solver
#[derive(Debug, Clone, Default)]
pub struct DecompositionConfig {
    /// Common engine settings (verbose, cancellation).
    pub base: ChcEngineConfig,
    /// PDR config for solving subproblems
    pub pdr_config: PdrConfig,
}

/// Decomposition solver for multi-predicate CHC problems.
pub(crate) struct DecompositionSolver {
    problem: ChcProblem,
    config: DecompositionConfig,
}

impl Drop for DecompositionSolver {
    fn drop(&mut self) {
        std::mem::take(&mut self.problem).iterative_drop();
    }
}

impl DecompositionSolver {
    /// Create a new decomposition solver.
    pub(crate) fn new(problem: ChcProblem, config: DecompositionConfig) -> Self {
        Self { problem, config }
    }

    /// Attempt to solve via decomposition.
    ///
    /// Returns `NotApplicable` if the problem cannot be decomposed
    /// (single SCC, no predicates, or single predicate).
    pub(crate) fn solve(&self) -> DecompositionResult {
        // Need at least 2 predicates for decomposition to be useful
        if self.problem.predicates().len() < 2 {
            return DecompositionResult::NotApplicable;
        }

        // Compute SCCs
        let scc_info = tarjan_scc(&self.problem);

        if self.config.base.verbose {
            safe_eprintln!(
                "Decomposition: {} predicates, {} SCCs",
                self.problem.predicates().len(),
                scc_info.sccs.len()
            );
        }

        // If single SCC, decomposition doesn't help
        if scc_info.sccs.len() <= 1 {
            return DecompositionResult::NotApplicable;
        }

        // Build SCC dependency graph and topological order
        let scc_order = match self.topological_order_sccs(&scc_info) {
            Some(order) => order,
            None => {
                // SCCs themselves form a cycle (shouldn't happen with Tarjan's)
                if self.config.base.verbose {
                    safe_eprintln!("Decomposition: SCC graph has cycle (unexpected)");
                }
                return DecompositionResult::NotApplicable;
            }
        };

        if self.config.base.verbose {
            safe_eprintln!("Decomposition: solving {} SCCs in order", scc_order.len());
            for (i, scc_idx) in scc_order.iter().enumerate() {
                let scc = &scc_info.sccs[*scc_idx];
                let pred_names: Vec<_> = scc
                    .predicates
                    .iter()
                    .filter_map(|id| self.problem.get_predicate(*id).map(|p| p.name.clone()))
                    .collect();
                safe_eprintln!(
                    "  {}: SCC {} ({} predicates, cyclic={}): {:?}",
                    i,
                    scc_idx,
                    scc.predicates.len(),
                    scc.is_cyclic,
                    pred_names
                );
            }
        }

        // Solve SCCs in topological order
        let mut known_invariants: FxHashMap<PredicateId, PredicateInterpretation> =
            FxHashMap::default();

        for scc_idx in scc_order {
            // Check for cooperative cancellation or memory budget (#2771)
            if self.config.base.is_cancelled() {
                return DecompositionResult::Unknown;
            }

            let scc = &scc_info.sccs[scc_idx];

            if self.config.base.verbose {
                let pred_names: Vec<_> = scc
                    .predicates
                    .iter()
                    .filter_map(|id| self.problem.get_predicate(*id).map(|p| p.name.clone()))
                    .collect();
                safe_eprintln!(
                    "Decomposition: solving SCC {} with predicates {:?}",
                    scc_idx,
                    pred_names
                );
            }

            // Extract and specialize subproblem
            let subproblem = match self.extract_subproblem(scc, &known_invariants) {
                Some(subproblem) => subproblem,
                None => {
                    // Internal consistency failure: dependency order violated, missing invariants,
                    // or invariant substitution failed. Fail-safe: return Unknown.
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "Decomposition: failed to extract subproblem for SCC {scc_idx}"
                        );
                    }
                    return DecompositionResult::Unknown;
                }
            };

            if self.config.base.verbose {
                safe_eprintln!(
                    "Decomposition: subproblem has {} clauses, {} predicates",
                    subproblem.clauses().len(),
                    subproblem.predicates().len()
                );
            }

            // Skip empty subproblems (predicate not used in any clause)
            if subproblem.clauses().is_empty() {
                if self.config.base.verbose {
                    safe_eprintln!("Decomposition: skipping empty subproblem");
                }
                // Set trivial invariant (true) for skipped predicates
                for pred_id in &scc.predicates {
                    if let Some(pred) = self.problem.get_predicate(*pred_id) {
                        let vars: Vec<_> = pred
                            .arg_sorts
                            .iter()
                            .enumerate()
                            .map(|(i, sort)| {
                                ChcVar::new(format!("__p{}_a{}", pred_id.index(), i), sort.clone())
                            })
                            .collect();
                        known_invariants.insert(
                            *pred_id,
                            PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
                        );
                    }
                }
                continue;
            }

            // Solve the subproblem with cancellation token propagated
            let mut pdr_config = self.config.pdr_config.clone();
            if let Some(token) = &self.config.base.cancellation_token {
                pdr_config.cancellation_token = Some(token.clone());
            }
            let mut solver = PdrSolver::new(subproblem.clone(), pdr_config);
            let result = solver.solve();

            match result {
                PdrResult::Safe(model) => {
                    // Record invariants from this SCC
                    for pred_id in &scc.predicates {
                        if let Some(interp) = model.get(pred_id) {
                            known_invariants.insert(*pred_id, interp.clone());
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "Decomposition: learned invariant for P{}: {}",
                                    pred_id.index(),
                                    interp.formula
                                );
                            }
                        } else if let Some(pred) = self.problem.get_predicate(*pred_id) {
                            // Predicate not in model (e.g., no clauses) - use true as fallback
                            let vars: Vec<_> = pred
                                .arg_sorts
                                .iter()
                                .enumerate()
                                .map(|(i, sort)| {
                                    ChcVar::new(
                                        format!("__p{}_a{}", pred_id.index(), i),
                                        sort.clone(),
                                    )
                                })
                                .collect();
                            known_invariants.insert(
                                *pred_id,
                                PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
                            );
                            if self.config.base.verbose {
                                safe_eprintln!(
                                    "Decomposition: using true as fallback invariant for P{}",
                                    pred_id.index()
                                );
                            }
                        }
                    }
                }
                PdrResult::Unsafe(cex) => {
                    if self.config.base.verbose {
                        safe_eprintln!("Decomposition: SCC {} is unsafe", scc_idx);
                    }
                    return DecompositionResult::Unsafe(cex);
                }
                PdrResult::Unknown | PdrResult::NotApplicable => {
                    if self.config.base.verbose {
                        safe_eprintln!("Decomposition: SCC {} returned unknown", scc_idx);
                    }
                    return DecompositionResult::Unknown;
                }
            }
        }

        // All SCCs solved - merge invariants
        let mut merged_model = InvariantModel::new();
        for (pred_id, interp) in known_invariants {
            merged_model.set(pred_id, interp);
        }

        // Verify the merged model against the full original problem.
        // Each SCC's PDR solver only verified its model against the subproblem.
        // The merged model must be verified against the full problem to catch
        // any bugs in SCC decomposition or invariant merging.
        // Pattern reference: case_split.rs:193-196
        //
        // #8630: Propagate cancellation token so the verifier bails when the
        // portfolio is cancelled or timed out, instead of hanging indefinitely.
        let mut verify_config = self.config.pdr_config.clone();
        if let Some(token) = &self.config.base.cancellation_token {
            verify_config.cancellation_token = Some(token.clone());
        }
        let mut verifier = PdrSolver::new(self.problem.clone(), verify_config);
        if verifier.verify_model(&merged_model) {
            DecompositionResult::Safe(merged_model)
        } else {
            if self.config.base.verbose {
                safe_eprintln!(
                    "Decomposition: merged model failed verification against original problem"
                );
            }
            DecompositionResult::Unknown
        }
    }

    /// Compute topological order of SCCs.
    ///
    /// SCCs are ordered so that if SCC A depends on SCC B (A uses predicates from B),
    /// then B comes before A in the order.
    fn topological_order_sccs(&self, scc_info: &SCCInfo) -> Option<Vec<usize>> {
        let n = scc_info.sccs.len();
        if n == 0 {
            return Some(Vec::new());
        }

        // Build SCC dependency graph: scc_a depends on scc_b if any predicate in scc_a
        // has a clause with a body predicate from scc_b
        let mut adj: Vec<FxHashSet<usize>> = vec![FxHashSet::default(); n];

        for clause in self.problem.clauses() {
            if let Some(head_pred) = clause.head.predicate_id() {
                if let Some(&head_scc) = scc_info.predicate_to_scc.get(&head_pred) {
                    for (body_pred, _) in &clause.body.predicates {
                        if let Some(&body_scc) = scc_info.predicate_to_scc.get(body_pred) {
                            // head_scc depends on body_scc
                            if head_scc != body_scc && !adj[head_scc].contains(&body_scc) {
                                adj[head_scc].insert(body_scc);
                            }
                        }
                    }
                }
            }
        }

        // Kahn's algorithm - solve leaves first (SCCs with no dependencies)
        // Uses adj[i].is_empty() as the "no remaining dependencies" check
        let mut queue: Vec<usize> = (0..n).filter(|&i| adj[i].is_empty()).collect();
        let mut result = Vec::with_capacity(n);

        while let Some(scc_idx) = queue.pop() {
            result.push(scc_idx);

            // Find SCCs that depend on this one and remove the dependency
            for (other_scc, adj_entry) in adj.iter_mut().enumerate() {
                if adj_entry.remove(&scc_idx) && adj_entry.is_empty() {
                    queue.push(other_scc);
                }
            }
        }

        if result.len() == n {
            Some(result)
        } else {
            None // Cycle detected
        }
    }

    /// Extract a subproblem for solving a single SCC.
    ///
    /// The subproblem contains:
    /// - Predicates from the SCC
    /// - Clauses that define or use predicates from the SCC
    /// - Known invariants substituted for predicates from other SCCs
    fn extract_subproblem(
        &self,
        scc: &PredicateSCC,
        known_invariants: &FxHashMap<PredicateId, PredicateInterpretation>,
    ) -> Option<ChcProblem> {
        let scc_preds: FxHashSet<PredicateId> = scc.predicates.iter().copied().collect();
        let mut subproblem = ChcProblem::new();

        // Declare predicates for this SCC
        let mut pred_map: FxHashMap<PredicateId, PredicateId> = FxHashMap::default();
        for &old_pred_id in &scc.predicates {
            if let Some(pred) = self.problem.get_predicate(old_pred_id) {
                let new_pred_id =
                    subproblem.declare_predicate(pred.name.clone(), pred.arg_sorts.clone());
                pred_map.insert(old_pred_id, new_pred_id);
            }
        }

        // Process clauses
        for clause in self.problem.clauses() {
            // Check if this clause is relevant to the SCC
            let head_in_scc = clause
                .head
                .predicate_id()
                .is_some_and(|id| scc_preds.contains(&id));
            let body_uses_scc = clause
                .body
                .predicates
                .iter()
                .any(|(id, _)| scc_preds.contains(id));
            let is_query = clause.is_query();

            // Include clause if:
            // 1. Head is in SCC (defining clause)
            // 2. Query clause that uses SCC predicates
            if !(head_in_scc || is_query && body_uses_scc) {
                continue;
            }

            // Substitute known invariants for body predicates not in this SCC
            let mut new_body_preds: Vec<(PredicateId, Vec<ChcExpr>)> = Vec::new();
            let mut extra_constraints: Vec<ChcExpr> = Vec::new();

            for (body_pred_id, body_args) in &clause.body.predicates {
                if scc_preds.contains(body_pred_id) {
                    // Predicate is in this SCC - keep it
                    // Invariant: predicates in this SCC must be in pred_map.
                    // If not, extraction is inconsistent. Fail-safe: return None.
                    let Some(&new_pred_id) = pred_map.get(body_pred_id) else {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "Decomposition: body predicate {:?} in SCC but not mapped",
                                body_pred_id
                            );
                        }
                        return None;
                    };
                    new_body_preds.push((new_pred_id, body_args.clone()));
                } else if let Some(interp) = known_invariants.get(body_pred_id) {
                    // Substitute known invariant
                    let Some(substituted) = self.substitute_interpretation(interp, body_args)
                    else {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "Decomposition: failed to substitute interpretation for predicate {:?}",
                                body_pred_id
                            );
                        }
                        return None;
                    };
                    extra_constraints.push(substituted);
                } else {
                    // Body predicate not in SCC and no known invariant.
                    // This indicates a bug in topological ordering or incomplete solving.
                    // Issue #1909: Previously silently dropped.
                    if self.config.base.verbose {
                        safe_eprintln!(
                            "Decomposition: body predicate {:?} not in SCC and no known invariant",
                            body_pred_id
                        );
                    }
                    return None;
                }
            }

            // Build new constraint
            let mut new_constraint = clause.body.constraint.clone();
            for extra in extra_constraints {
                new_constraint = match new_constraint {
                    Some(c) => Some(ChcExpr::and(c, extra)),
                    None => Some(extra),
                };
            }

            // Build new head
            // Issue #1909: Head predicate must be in pred_map - if not, fail-safe.
            let new_head = match &clause.head {
                ClauseHead::Predicate(pred_id, args) => {
                    let Some(&new_pred_id) = pred_map.get(pred_id) else {
                        if self.config.base.verbose {
                            safe_eprintln!(
                                "Decomposition: head predicate {:?} not in pred_map",
                                pred_id
                            );
                        }
                        return None;
                    };
                    ClauseHead::Predicate(new_pred_id, args.clone())
                }
                ClauseHead::False => ClauseHead::False,
            };

            let new_clause =
                HornClause::new(ClauseBody::new(new_body_preds, new_constraint), new_head);
            subproblem.add_clause(new_clause);
        }

        Some(subproblem)
    }

    /// Substitute a predicate interpretation with given arguments.
    ///
    /// Given invariant `P(v0, v1) := formula(v0, v1)` and arguments `[a, b]`,
    /// returns `formula(a, b)` with variables substituted.
    fn substitute_interpretation(
        &self,
        interp: &PredicateInterpretation,
        args: &[ChcExpr],
    ) -> Option<ChcExpr> {
        if interp.vars.len() != args.len() {
            // Arity mismatch indicates bug in problem construction or invariant synthesis.
            // Issue #1910: Previously returned `true` fallback.
            if self.config.base.verbose {
                safe_eprintln!(
                    "Decomposition: arity mismatch in substitute_interpretation: {} vars vs {} args for {:?}",
                    interp.vars.len(),
                    args.len(),
                    interp
                );
            }
            return None;
        }

        let subst: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .cloned()
            .zip(args.iter().cloned())
            .collect();

        Some(interp.formula.substitute(&subst))
    }
}
