// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover step-bounded difference invariants from loop guards.
    ///
    /// For self-loops with pattern:
    /// - Guard: var_i < var_j (or equivalently NOT (var_j <= var_i))
    /// - Increment: var_i' = var_i + step (step > 0)
    ///
    /// We can infer the invariant: var_i < var_j + step
    ///
    /// This is inductive because:
    /// - At init: if var_i < var_j then var_i < var_j + step (for positive step)
    /// - At transition: if var_i < var_j + step and guard (var_i < var_j),
    ///   then var_i' = var_i + step < var_j + step (because var_i < var_j)
    ///
    /// This is crucial for benchmarks like s_multipl_11 where A increases by 1000
    /// with guard A < B, giving invariant A < B + 1000.
    pub(in crate::pdr::solver) fn discover_step_bounded_difference_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect step-bounded difference candidates
        let mut candidates: Vec<(PredicateId, ChcVar, ChcVar, i128)> = Vec::new();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Look at self-loop transitions for this predicate
            for clause in self.problem.clauses_defining(pred.id) {
                // Must be a self-loop (same predicate in body)
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];
                if *body_pred != pred.id {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                if head_args.len() != canonical_vars.len()
                    || body_args.len() != canonical_vars.len()
                {
                    continue;
                }

                // Build mapping from body variable names to canonical indices
                // #2492: Also extract constituent vars from expression body args
                let mut body_to_canon_idx: FxHashMap<String, usize> = FxHashMap::default();
                for (idx, body_arg) in body_args.iter().enumerate() {
                    match body_arg {
                        ChcExpr::Var(v) => {
                            body_to_canon_idx.insert(v.name.clone(), idx);
                        }
                        expr => {
                            for v in expr.vars() {
                                body_to_canon_idx.entry(v.name.clone()).or_insert(idx);
                            }
                        }
                    }
                }

                // Extract guard patterns and increment patterns from constraint
                let constraint = match &clause.body.constraint {
                    Some(c) => c.clone(),
                    None => continue,
                };

                // Look for guard patterns: NOT (var_j <= var_i) meaning var_i < var_j
                // And increment patterns: var_i' = var_i + step
                for (canon_idx, canon_var) in canonical_vars.iter().enumerate() {
                    if self.is_cancelled() {
                        return;
                    }
                    if !matches!(canon_var.sort, ChcSort::Int) {
                        continue;
                    }

                    // Get the body variable name for this canonical index
                    let body_var_name = body_args.get(canon_idx).and_then(|e| {
                        if let ChcExpr::Var(v) = e {
                            Some(v.name.clone())
                        } else {
                            None
                        }
                    });
                    let body_var_name = match body_var_name {
                        Some(n) => n,
                        None => continue,
                    };

                    // Get the head expression for this variable (post-transition value)
                    let head_expr = &head_args[canon_idx];

                    // Check if head_expr = body_var + step
                    let step = Self::extract_addition_offset(head_expr, &body_var_name);
                    let step = match step {
                        Some(s) if s > 0 => s,
                        _ => continue,
                    };

                    // Look for guard: NOT (other_var <= body_var) in the constraint
                    // which means body_var < other_var
                    let guard_var = Self::extract_lt_guard_other_var(&constraint, &body_var_name);
                    if let Some(other_body_var) = guard_var {
                        // Find the canonical index of the other variable
                        if let Some(&other_canon_idx) = body_to_canon_idx.get(&other_body_var) {
                            if other_canon_idx < canonical_vars.len() {
                                let other_canon_var = &canonical_vars[other_canon_idx];
                                // We found: var_i < var_j (guard) and var_i' = var_i + step
                                // Candidate invariant: var_i < var_j + step
                                candidates.push((
                                    pred.id,
                                    canon_var.clone(),
                                    other_canon_var.clone(),
                                    step,
                                ));
                            }
                        }
                    }
                }
            }
        }

        // Process candidates
        for (predicate, var_i, var_j, step) in candidates {
            // Invariant: var_i < var_j + step  (equivalently var_i - var_j < step)
            let bound_expr = ChcExpr::add(ChcExpr::var(var_j.clone()), ChcExpr::Int(step));
            let invariant = ChcExpr::lt(ChcExpr::var(var_i.clone()), bound_expr);

            // Check if already known
            let already_known = self.frames.len() > 1
                && self.frames[1]
                    .lemmas
                    .iter()
                    .any(|l| l.predicate == predicate && l.formula == invariant);
            if already_known {
                continue;
            }

            // Verify the invariant is valid at init
            if !self.is_step_bounded_valid_at_init(predicate, &var_i, &var_j, step) {
                continue;
            }

            // Verify the invariant is preserved by transitions
            if !self.is_step_bounded_preserved(predicate, &var_i, &var_j, step) {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Discovered step-bounded invariant for pred {}: {} < {} + {}",
                    predicate.index(),
                    var_i.name,
                    var_j.name,
                    step,
                );
            }

            self.add_discovered_invariant(predicate, invariant, 1);
        }

        // Phase 2: Propagate step-bounded invariants to target predicates via cross-predicate transitions
        self.propagate_step_bounded_to_targets();
    }

    /// Propagate step-bounded invariants from source predicates to target predicates
    pub(in crate::pdr::solver) fn propagate_step_bounded_to_targets(&mut self) {
        if self.frames.len() <= 1 {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Collect step-bounded invariants and their mappings
        let mut to_propagate: Vec<(PredicateId, ChcVar, ChcVar, i128)> = Vec::new();

        for target_pred in &predicates {
            let target_vars = match self.canonical_vars(target_pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Find cross-predicate transitions to this target
            for clause in self.problem.clauses_defining(target_pred.id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (source_pred, source_args) = &clause.body.predicates[0];
                if *source_pred == target_pred.id {
                    continue; // Skip self-loops
                }

                let source_vars = match self.canonical_vars(*source_pred) {
                    Some(v) => v.to_vec(),
                    None => continue,
                };

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                if head_args.len() != target_vars.len() {
                    continue;
                }

                // Look for step-bounded invariants on the source predicate
                let source_step_bounded: Vec<_> = self.frames[1]
                    .lemmas
                    .iter()
                    .filter(|l| l.predicate == *source_pred)
                    .filter_map(|l| {
                        // Look for pattern: var_i < var_j + step
                        if let ChcExpr::Op(ChcOp::Lt, args) = &l.formula {
                            if args.len() == 2 {
                                if let ChcExpr::Var(var_i) = args[0].as_ref() {
                                    if let ChcExpr::Op(ChcOp::Add, add_args) = args[1].as_ref() {
                                        if add_args.len() == 2 {
                                            if let (ChcExpr::Var(var_j), ChcExpr::Int(step)) =
                                                (add_args[0].as_ref(), add_args[1].as_ref())
                                            {
                                                return Some((
                                                    var_i.name.clone(),
                                                    var_j.name.clone(),
                                                    *step,
                                                ));
                                            }
                                        }
                                    }
                                }
                            }
                        }
                        None
                    })
                    .collect();

                for (src_var_i_name, src_var_j_name, step) in source_step_bounded {
                    // Find the source variable indices
                    let src_i_idx = source_vars.iter().position(|v| v.name == src_var_i_name);
                    let src_j_idx = source_vars.iter().position(|v| v.name == src_var_j_name);

                    let (src_i, src_j) = match (src_i_idx, src_j_idx) {
                        (Some(i), Some(j)) => (i, j),
                        _ => continue,
                    };

                    // Get the expressions that map to target variables
                    // source_args[src_i] maps to source_vars[src_i]
                    // head_args[tgt_k] defines target_vars[tgt_k]
                    // We need to find which target vars receive the source vars

                    // Build reverse mapping: source var name -> target var index
                    let src_arg_i = source_args.get(src_i);
                    let src_arg_j = source_args.get(src_j);

                    if src_arg_i.is_none() || src_arg_j.is_none() {
                        continue;
                    }

                    // Find which head_args contain the source vars
                    // head_args[k] = expression involving source_args
                    // We want head_args[k] = source_var directly (simple mapping)
                    // #2492: Also handle expression source/head args by extracting vars
                    let mut tgt_i_idx = None;
                    let mut tgt_j_idx = None;

                    // Extract primary var name from source args (may be expressions)
                    let src_name_i = src_arg_i.and_then(|a| match a {
                        ChcExpr::Var(v) => Some(v.name.clone()),
                        expr => expr.vars().into_iter().next().map(|v| v.name),
                    });
                    let src_name_j = src_arg_j.and_then(|a| match a {
                        ChcExpr::Var(v) => Some(v.name.clone()),
                        expr => expr.vars().into_iter().next().map(|v| v.name),
                    });

                    if let (Some(name_i), Some(name_j)) = (&src_name_i, &src_name_j) {
                        for (tgt_idx, head_arg) in head_args.iter().enumerate() {
                            // Check direct Var match or first var inside expression
                            let head_var_name: Option<String> = match head_arg {
                                ChcExpr::Var(hv) => Some(hv.name.clone()),
                                expr => expr.vars().first().map(|v| v.name.clone()),
                            };
                            if let Some(ref hname) = head_var_name {
                                if hname == name_i && tgt_i_idx.is_none() {
                                    tgt_i_idx = Some(tgt_idx);
                                }
                                if hname == name_j && tgt_j_idx.is_none() {
                                    tgt_j_idx = Some(tgt_idx);
                                }
                            }
                        }
                    }

                    let (tgt_i, tgt_j) = match (tgt_i_idx, tgt_j_idx) {
                        (Some(i), Some(j)) => (i, j),
                        _ => continue,
                    };

                    if tgt_i < target_vars.len() && tgt_j < target_vars.len() {
                        to_propagate.push((
                            target_pred.id,
                            target_vars[tgt_i].clone(),
                            target_vars[tgt_j].clone(),
                            step,
                        ));
                    }
                }
            }
        }

        // Add propagated invariants
        for (predicate, var_i, var_j, step) in to_propagate {
            let bound_expr = ChcExpr::add(ChcExpr::var(var_j.clone()), ChcExpr::Int(step));
            let invariant = ChcExpr::lt(ChcExpr::var(var_i.clone()), bound_expr);

            // Check if already known
            let already_known = self.frames[1]
                .lemmas
                .iter()
                .any(|l| l.predicate == predicate && l.formula == invariant);
            if already_known {
                continue;
            }

            // Verify preservation by self-transitions
            if !self.is_step_bounded_preserved(predicate, &var_i, &var_j, step) {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Propagated step-bounded invariant for pred {} (from source): {} < {} + {}",
                    predicate.index(),
                    var_i.name,
                    var_j.name,
                    step,
                );
            }

            self.add_discovered_invariant(predicate, invariant, 1);
        }

        // Phase 3: Discover linear combination bounds for target predicates
        // Pattern: If source has var_a < var_b + K, and target has:
        //   - var_a_tgt = var_a (fixed)
        //   - var_b_tgt increments by step_b per iteration
        //   - var_c_tgt increments by step_c per iteration
        // Then: var_a_tgt + (step_b/step_c)*var_c_tgt - var_b_tgt is constant (= var_a - var_b at entry)
        // And: var_a_tgt + coeff*var_c_tgt - var_b_tgt < K
        self.discover_linear_combination_bounds();
    }
}
