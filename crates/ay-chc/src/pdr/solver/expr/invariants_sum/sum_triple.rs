// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Returns propagated sum-equals-var invariants for chain orchestration.
    pub(in crate::pdr::solver) fn discover_triple_sum_invariants(
        &mut self,
    ) -> Vec<(PredicateId, usize, usize, usize)> {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Track discovered triple sums for cross-predicate propagation:
        // (pred_id, idx_i, idx_j, idx_k, idx_l) where i+j+k = l
        let mut discovered_triples: Vec<(PredicateId, usize, usize, usize, usize)> = Vec::new();

        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            // Skip predicates with incoming inter-predicate transitions.
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 4 variables for a triple sum invariant
            if canonical_vars.len() < 4 {
                continue;
            }

            // Skip predicates with many variables — triple-sum is O(n^4) and the
            // candidate space grows as C(n,3)*(n-3). For n=10: 840 candidates,
            // n=15: 3185, n=20: 19380. Cap at 10 to keep startup fast (#2816).
            let int_var_count = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, ChcSort::Int))
                .count();
            if int_var_count > 10 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Skipping triple-sum discovery for pred {} ({} int vars > 10 threshold)",
                        pred.id.index(),
                        int_var_count,
                    );
                }
                continue;
            }

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Find quadruples (i, j, k, l) where var_i + var_j + var_k = var_l
            for i in 0..canonical_vars.len() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return Vec::new();
                }
                for j in (i + 1)..canonical_vars.len() {
                    for k in (j + 1)..canonical_vars.len() {
                        for l in 0..canonical_vars.len() {
                            // Skip if l is one of i, j, k
                            if l == i || l == j || l == k {
                                continue;
                            }

                            let var_i = &canonical_vars[i];
                            let var_j = &canonical_vars[j];
                            let var_k = &canonical_vars[k];
                            let var_l = &canonical_vars[l];

                            // Only check integer variables
                            if !matches!(var_i.sort, ChcSort::Int)
                                || !matches!(var_j.sort, ChcSort::Int)
                                || !matches!(var_k.sort, ChcSort::Int)
                                || !matches!(var_l.sort, ChcSort::Int)
                            {
                                continue;
                            }

                            // Check if all have constant initial values
                            let init_i = init_values.get(&var_i.name);
                            let init_j = init_values.get(&var_j.name);
                            let init_k = init_values.get(&var_k.name);
                            let init_l = init_values.get(&var_l.name);

                            // Try the simple case: all constants
                            let holds_at_init = match (init_i, init_j, init_k, init_l) {
                                (Some(bi), Some(bj), Some(bk), Some(bl))
                                    if bi.min == bi.max
                                        && bj.min == bj.max
                                        && bk.min == bk.max
                                        && bl.min == bl.max =>
                                {
                                    bi.min + bj.min + bk.min == bl.min
                                }
                                _ => {
                                    // Symbolic case: use SMT to check if init implies sum
                                    // Common pattern: (a0 = a1) AND (a2 = 0) AND (a3 = 0)
                                    // => a0 + a2 + a3 = a1
                                    self.check_triple_sum_holds_at_init(
                                        pred.id, var_i, var_j, var_k, var_l,
                                    )
                                }
                            };

                            if !holds_at_init {
                                if self.config.verbose
                                    && (var_j.name.ends_with("a2") || var_j.name.ends_with("a3"))
                                {
                                    safe_eprintln!(
                                        "PDR: Triple sum ({} + {} + {} = {}) fails init check",
                                        var_i.name,
                                        var_j.name,
                                        var_k.name,
                                        var_l.name
                                    );
                                }
                                continue;
                            }

                            // Check if this relationship is preserved by transitions
                            if !self.is_triple_sum_preserved_by_transitions(
                                pred.id, var_i, var_j, var_k, var_l,
                            ) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Triple sum ({} + {} + {} = {}) is NOT preserved by transition",
                                        var_i.name, var_j.name, var_k.name, var_l.name
                                    );
                                }
                                continue;
                            }

                            // Found a valid triple sum invariant!
                            discovered_triples.push((pred.id, i, j, k, l));

                            let sum_expr = ChcExpr::add(
                                ChcExpr::add(
                                    ChcExpr::var(var_i.clone()),
                                    ChcExpr::var(var_j.clone()),
                                ),
                                ChcExpr::var(var_k.clone()),
                            );
                            let triple_sum_invariant =
                                ChcExpr::eq(sum_expr, ChcExpr::var(var_l.clone()));

                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered triple sum invariant for pred {}: {} + {} + {} = {}",
                                    pred.id.index(),
                                    var_i.name,
                                    var_j.name,
                                    var_k.name,
                                    var_l.name
                                );
                            }

                            // Add to frame 1 — use algebraic variant since
                            // is_triple_sum_preserved_by_transitions verifies via
                            // algebraic analysis (bypasses SMT Unknown issue #955).
                            self.add_discovered_invariant_algebraic(
                                pred.id,
                                triple_sum_invariant,
                                1,
                            );
                        }
                    }
                }
            }
        }

        // Phase 2: Propagate triple sums across inter-predicate transitions.
        //
        // When source predicate has i+j+k = l and an inter-predicate transition
        // constrains one of {i,j,k} to 0, the triple sum specializes to a 2-var
        // sum-equals-var invariant in the target predicate.
        //
        // Example: s_multipl_15 — PRE has A+B+C = v_1. PRE→POST with A=0 gives
        // B+C = v_1, which maps to POST's sum-equals-var invariant.
        // Part of #3121
        self.propagate_triple_sums_across_edges(&discovered_triples)
    }

    /// Propagate triple sum invariants across inter-predicate transitions.
    ///
    /// When a source predicate has `var_i + var_j + var_k = var_l` and a clause
    /// `Source(args) ∧ constraint ⟹ Target(args')` constrains one of the summed
    /// variables to 0, the triple sum specializes to a 2-var sum-equals-var
    /// invariant `var_a + var_b = var_c` in the target predicate.
    ///
    /// Part of #3121 — recovers s_multipl_15/16/18 where PRE has a triple sum
    /// but POST needs the specialized sum-equals-var.
    pub(in crate::pdr::solver) fn propagate_triple_sums_across_edges(
        &mut self,
        discovered_triples: &[(PredicateId, usize, usize, usize, usize)],
    ) -> Vec<(PredicateId, usize, usize, usize)> {
        let mut propagated_sev: Vec<(PredicateId, usize, usize, usize)> = Vec::new();
        if discovered_triples.is_empty() {
            return propagated_sev;
        }

        // Collect propagation candidates to avoid borrow conflicts.
        // Each candidate: (head_pred, head_var_a_idx, head_var_b_idx, head_var_c_idx)
        // representing the specialized sum-equals-var: a + b = c
        let mut candidates: Vec<(PredicateId, usize, usize, usize)> = Vec::new();

        for clause in self.problem.clauses() {
            // Must have exactly one body predicate
            if clause.body.predicates.len() != 1 {
                continue;
            }

            let (head_pred, head_args) = match &clause.head {
                crate::ClauseHead::Predicate(p, args) => (*p, args),
                crate::ClauseHead::False => continue,
            };

            let (body_pred, body_args) = &clause.body.predicates[0];

            // Skip self-transitions
            if head_pred == *body_pred {
                continue;
            }

            // Extract equality constraints (var = constant) from clause constraint.
            // Look for patterns like (= A 0) or (and ... (= A 0) ...).
            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let zero_constrained = Self::extract_zero_constrained_vars(&constraint, body_args);

            if zero_constrained.is_empty() {
                continue;
            }

            // Build body_arg_name → head_idx mapping for variable propagation
            let mut body_idx_to_head_idx: FxHashMap<usize, usize> = FxHashMap::default();
            for (h_idx, head_arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(hv) = head_arg {
                    for (b_idx, body_arg) in body_args.iter().enumerate() {
                        if let ChcExpr::Var(bv) = body_arg {
                            if hv.name == bv.name {
                                body_idx_to_head_idx.insert(b_idx, h_idx);
                                break;
                            }
                        }
                    }
                }
            }

            // For each discovered triple sum, try to specialize
            for &(src_pred, idx_i, idx_j, idx_k, idx_l) in discovered_triples {
                if src_pred != *body_pred {
                    continue;
                }

                // Map source canonical indices to body arg indices.
                // Body args are positionally aligned with the predicate's canonical
                // vars: body_args[i] corresponds to canonical var i.
                let src_to_body = |src_idx: usize| -> Option<usize> {
                    if src_idx < body_args.len() {
                        Some(src_idx)
                    } else {
                        None
                    }
                };

                let b_i = src_to_body(idx_i);
                let b_j = src_to_body(idx_j);
                let b_k = src_to_body(idx_k);
                let b_l = src_to_body(idx_l);

                // Check which of the three summed variables (i, j, k) is zero-constrained
                let summed = [(b_i, idx_i), (b_j, idx_j), (b_k, idx_k)];
                for (s_idx, &(b_pos, _src_idx)) in summed.iter().enumerate() {
                    let b_pos = match b_pos {
                        Some(p) => p,
                        None => continue,
                    };

                    if !zero_constrained.contains(&b_pos) {
                        continue;
                    }

                    // This summed variable is 0 at the transition.
                    // The other two summed vars + the RHS var form the candidate.
                    let remaining: Vec<Option<usize>> = summed
                        .iter()
                        .enumerate()
                        .filter(|(i, _)| *i != s_idx)
                        .map(|(_, &(b, _))| b)
                        .collect();

                    let (rem_a, rem_b) = match (remaining.first(), remaining.get(1)) {
                        (Some(Some(a)), Some(Some(b))) => (*a, *b),
                        _ => continue,
                    };
                    let rhs = match b_l {
                        Some(l) => l,
                        None => continue,
                    };

                    // Map to head predicate indices
                    let h_a = body_idx_to_head_idx.get(&rem_a);
                    let h_b = body_idx_to_head_idx.get(&rem_b);
                    let h_c = body_idx_to_head_idx.get(&rhs);

                    if let (Some(&ha), Some(&hb), Some(&hc)) = (h_a, h_b, h_c) {
                        candidates.push((head_pred, ha, hb, hc));
                    }
                }
            }
        }

        // Process candidates with mutable access to self
        for (head_pred, h_a, h_b, h_c) in candidates {
            let head_vars = match self.canonical_vars(head_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if h_a >= head_vars.len() || h_b >= head_vars.len() || h_c >= head_vars.len() {
                continue;
            }

            let va = &head_vars[h_a];
            let vb = &head_vars[h_b];
            let vc = &head_vars[h_c];

            // Verify: sum preserved by target's self-loop transitions
            if !self.sum_eq_var_preserved(head_pred, va, vb, vc) {
                continue;
            }

            let inv = ChcExpr::eq(
                ChcExpr::add(ChcExpr::var(va.clone()), ChcExpr::var(vb.clone())),
                ChcExpr::var(vc.clone()),
            );

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Propagated triple-sum → sum-equals-var from source to pred {}: {} + {} = {}",
                    head_pred.index(),
                    va.name,
                    vb.name,
                    vc.name
                );
            }

            self.add_discovered_invariant_algebraic(head_pred, inv, 1);

            // Track for further propagation (double→equality chain)
            propagated_sev.push((head_pred, h_a, h_b, h_c));
        }

        propagated_sev
    }
}
