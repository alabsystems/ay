// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Propagate symbolic equality constraints through inter-predicate transitions.
    ///
    /// For phase-chain benchmarks like gj2007, equality constraints like `B = C` must
    /// propagate from source predicates to target predicates across transitions.
    /// The forward must-summary propagation only propagates concrete points, not symbolic
    /// constraints. This function fills that gap.
    ///
    /// For each inter-predicate transition (P -> Q where P != Q):
    /// 1. Extract equality constraints `arg_i = arg_j` from P's must-summary
    /// 2. Check if both args are preserved through the transition
    /// 3. If so, add the equality as a frame[0] lemma for Q
    ///
    /// Part of #1613: Must-summary self-loop closure for inter-predicate propagation.
    pub(in crate::pdr::solver) fn propagate_symbolic_equalities_to_derived_predicates(&mut self) {
        if !self.config.use_must_summaries {
            return;
        }

        // Collect predicates with must-summaries or frame[1] lemmas (sources of equalities)
        let preds_with_equalities: Vec<PredicateId> = self
            .problem
            .predicates()
            .iter()
            .enumerate()
            .filter_map(|(idx, _)| {
                let pred = PredicateId::new(idx as u32);
                // Include predicate if it has must-summaries OR frame[1] lemmas
                let has_must = self.reachability.must_summaries.get(0, pred).is_some();
                let has_frame1 = self.frames.len() > 1
                    && self.frames[1].lemmas.iter().any(|l| l.predicate == pred);
                if has_must || has_frame1 {
                    Some(pred)
                } else {
                    None
                }
            })
            .collect();

        for src_pred in preds_with_equalities {
            // Get must-summary if available (may be None for predicates with only frame[1] lemmas).
            // Use backed-only summaries to avoid propagating equalities from heuristic seeds (#2247).
            let must_summary = self.reachability.must_summaries.get_backed(0, src_pred);

            let src_canonical_vars = match self.canonical_vars(src_pred).map(<[ChcVar]>::to_vec) {
                Some(v) => v,
                None => continue,
            };

            // Extract equality constraints (arg_i = arg_j) from must-summary and frame[1] lemmas
            let mut equalities: Vec<(usize, usize)> = Vec::new();

            // Check must-summary if available
            if let Some(ref ms) = must_summary {
                for i in 0..src_canonical_vars.len() {
                    for j in (i + 1)..src_canonical_vars.len() {
                        if Self::has_equality_in_formula(ms, i, j, &src_canonical_vars) {
                            equalities.push((i, j));
                        }
                    }
                }
                // (#7048) Derive transitive equalities from shared constants.
                // If the must-summary says var_i = C and var_j = C for the same
                // constant C, then var_i = var_j. This catches dillig02_m where
                // the init state has a3=0 and a4=0 but no direct a3=a4 equality.
                let const_map = Self::extract_var_const_equalities(ms, &src_canonical_vars);
                let mut by_const: FxHashMap<i128, Vec<usize>> = FxHashMap::default();
                for (idx, val) in &const_map {
                    by_const.entry(*val).or_default().push(*idx);
                }
                for indices in by_const.values() {
                    for wi in 0..indices.len() {
                        for wj in (wi + 1)..indices.len() {
                            let pair = (indices[wi], indices[wj]);
                            if !equalities.contains(&pair) {
                                equalities.push(pair);
                            }
                        }
                    }
                }
            }

            // Also check frame index 1 lemmas for equalities since
            // discover_equality_invariants adds equalities to frames, not must_summaries.
            if self.frames.len() > 1 {
                for lemma in &self.frames[1].lemmas {
                    if lemma.predicate == src_pred {
                        for i in 0..src_canonical_vars.len() {
                            for j in (i + 1)..src_canonical_vars.len() {
                                let pair = (i, j);
                                if !equalities.contains(&pair)
                                    && Self::has_equality_in_formula(
                                        &lemma.formula,
                                        i,
                                        j,
                                        &src_canonical_vars,
                                    )
                                {
                                    equalities.push(pair);
                                }
                            }
                        }
                    }
                }
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Found {} equalities in pred {} (must-summary + frame[1]): {:?}",
                    equalities.len(),
                    src_pred.index(),
                    equalities
                );
            }

            if equalities.is_empty() {
                continue;
            }

            // Collect candidate propagations first to avoid borrow issues with is_self_inductive_blocking
            let mut candidates: Vec<(PredicateId, ChcExpr)> = Vec::new();

            // Find inter-predicate transitions FROM this predicate
            for clause in self.problem.clauses() {
                // Check if body contains this predicate
                let body_entry = clause.body.predicates.iter().find(|(p, _)| *p == src_pred);
                let Some((_, body_args)) = body_entry else {
                    continue;
                };

                // Check if head is a different predicate
                let (target_pred, head_args) = match &clause.head {
                    crate::ClauseHead::Predicate(p, args) if *p != src_pred => {
                        (*p, args.as_slice())
                    }
                    _ => continue,
                };

                let target_canonical_vars =
                    match self.canonical_vars(target_pred).map(<[ChcVar]>::to_vec) {
                        Some(v) => v,
                        None => continue,
                    };

                // For each equality in source, check if it propagates to target
                for &(src_i, src_j) in &equalities {
                    // Find which body args correspond to src_i and src_j
                    if src_i >= body_args.len() || src_j >= body_args.len() {
                        continue;
                    }

                    let body_arg_i = &body_args[src_i];
                    let body_arg_j = &body_args[src_j];

                    // Find where these body args appear in the head args
                    // The transition maps body -> head, so we need to track which
                    // head argument equals which body argument.
                    //
                    // Case 1: body_arg_i is a variable that appears as head_arg[k]
                    // Case 2: body_arg_i == head_arg[k] (identity)
                    let head_idx_i = self.find_head_arg_for_body_arg(body_arg_i, head_args, clause);
                    let head_idx_j = self.find_head_arg_for_body_arg(body_arg_j, head_args, clause);

                    if let (Some(hi), Some(hj)) = (head_idx_i, head_idx_j) {
                        if hi < target_canonical_vars.len() && hj < target_canonical_vars.len() {
                            // The equality propagates: target_arg[hi] = target_arg[hj]
                            let eq = ChcExpr::eq(
                                ChcExpr::var(target_canonical_vars[hi].clone()),
                                ChcExpr::var(target_canonical_vars[hj].clone()),
                            );
                            candidates.push((target_pred, eq));
                        }
                    }
                }
            }

            // Now verify each candidate with is_self_inductive_blocking and add if valid
            for (target_pred, eq) in candidates {
                // Check self-inductiveness: is_self_inductive_blocking checks if NOT(eq) is preserved,
                // so passing NOT(eq) checks if eq is an invariant.
                // Self-audit fix #1613: sound propagation requires this check.
                let not_eq = ChcExpr::not(eq.clone());
                if !self.is_self_inductive_blocking(&not_eq, target_pred) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Propagated equality {} not self-inductive on pred {}, trying weakened inequalities",
                            eq,
                            target_pred.index()
                        );
                    }
                    // D1 (#1362): Weaken equality to pair of inequalities and try each half.
                    // Reference: Z3 expand_literals in spacer_util.cpp:319-374.
                    // When x = y fails self-inductiveness, try x >= y and x <= y independently.
                    // Route through add_discovered_invariant to get proper init-validity
                    // checks and frame[1] insertion (matching equality propagation in
                    // discovery.rs:256). Direct frame[0] insertion skips init-validity
                    // and requires push_lemmas to reach frame[1] for model building.
                    if let ChcExpr::Op(ChcOp::Eq, ref args) = eq {
                        if args.len() == 2 {
                            let lhs = (*args[0]).clone();
                            let rhs = (*args[1]).clone();
                            // Try lhs >= rhs (expressed as rhs <= lhs)
                            let ge_ineq = ChcExpr::le(rhs.clone(), lhs.clone());
                            let added_ge =
                                self.add_discovered_invariant(target_pred, ge_ineq.clone(), 1);
                            if added_ge && self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated weakened >= from pred {} to pred {}: {}",
                                    src_pred.index(),
                                    target_pred.index(),
                                    ge_ineq
                                );
                            }
                            // Try lhs <= rhs
                            let le_ineq = ChcExpr::le(lhs, rhs);
                            let added_le =
                                self.add_discovered_invariant(target_pred, le_ineq.clone(), 1);
                            if added_le && self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Propagated weakened <= from pred {} to pred {}: {}",
                                    src_pred.index(),
                                    target_pred.index(),
                                    le_ineq
                                );
                            }
                        }
                    }
                    continue;
                }

                // Route through the unified lemma insertion path (#2459 Phase 1).
                let lemma = Lemma::new(target_pred, eq.clone(), 0);
                self.add_lemma_to_frame(lemma, 0);
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Propagated equality from pred {} to pred {}: {}",
                        src_pred.index(),
                        target_pred.index(),
                        eq
                    );
                }
            }
        }
    }

    /// Find which head argument index corresponds to a body argument through the transition.
    ///
    /// For a clause like: P(A, B, C) ∧ guard -> Q(A, B, C)
    /// If body_arg is the variable "A", this returns the index where "A" appears in head_args.
    fn find_head_arg_for_body_arg(
        &self,
        body_arg: &ChcExpr,
        head_args: &[ChcExpr],
        clause: &HornClause,
    ) -> Option<usize> {
        // Case 1: body_arg is a variable that appears directly in head_args
        if let ChcExpr::Var(body_var) = body_arg {
            for (idx, head_arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(head_var) = head_arg {
                    if body_var.name == head_var.name {
                        return Some(idx);
                    }
                }
            }
        }

        // Case 2: Check if body_arg equals a head_arg through the constraint
        // For example: if constraint has (= D A), and head_arg[k] is D, then body_arg A -> k
        // This is complex, so we only handle the direct variable case for now.
        let _ = clause; // Suppress warning about unused parameter

        None
    }

    /// Compute mixed edge summary for hyperedge (clause with multiple body predicates).
    ///
    /// For a clause with body predicates [P1, P2, ..., Pn], this combines:
    /// - May-summaries (over-approximations/frame constraints) for predicates 0..=last_may_index
    /// - Must-summaries (under-approximations) for predicates (last_may_index+1)..n
    ///
    /// This is the Spacer technique for handling non-linear CHC clauses.
    ///
    /// Returns: (clause_constraint ∧ may_summaries ∧ must_summaries, predicate_to_refine_args)
    pub(in crate::pdr::solver) fn get_edge_mixed_summary(
        &self,
        clause: &HornClause,
        level: usize,
        last_may_index: usize,
    ) -> Option<(ChcExpr, PredicateId, Vec<ChcExpr>)> {
        let body_predicates = &clause.body.predicates;
        if body_predicates.is_empty() || last_may_index >= body_predicates.len() {
            return None;
        }

        let mut components = Vec::new();

        // Add may-summaries (frame constraints) for predicates 0..=last_may_index
        for (pred, args) in body_predicates.iter().take(last_may_index + 1) {
            let frame_constraint = self.frames[level]
                .get_predicate_constraint(*pred)
                .unwrap_or(ChcExpr::Bool(true));
            if let Some(frame_on_body) = self.apply_to_args(*pred, &frame_constraint, args) {
                components.push(frame_on_body);
            }
        }

        // Add must-summaries for predicates (last_may_index+1)..n
        for (pred, args) in body_predicates.iter().skip(last_may_index + 1) {
            if let Some(must_summary) = self.reachability.must_summaries.get(level, *pred) {
                if let Some(must_on_body) = self.apply_to_args(*pred, &must_summary, args) {
                    components.push(must_on_body);
                }
            } else {
                // No must-summary available -> use false (no definitely reachable states)
                // This will make the query UNSAT if we need must-summary for this predicate
                components.push(ChcExpr::Bool(false));
            }
        }

        // Add clause constraint (transition relation)
        let clause_constraint = match clause.body.constraint.as_ref() {
            Some(c) => c.clone(),
            None => ChcExpr::Bool(true),
        };
        components.push(clause_constraint);

        let combined = if components.is_empty() {
            ChcExpr::Bool(true)
        } else {
            components
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true))
        };

        // Return the predicate to refine (the one at last_may_index)
        let (refine_pred, refine_args) = &body_predicates[last_may_index];
        Some((combined, *refine_pred, refine_args.clone()))
    }
}
