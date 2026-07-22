// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Three-variable difference bound invariant discovery.
//!
//! Discovers invariants of the form `D >= B - A` from init constraints
//! and verifies their preservation by transitions.

use super::*;

impl PdrSolver {
    /// Discover three-variable difference bound invariants of the form: var_d >= var_b - var_a
    ///
    /// These are extracted from init constraints like `(>= D (+ B (* (- 1) A)))` which
    /// represents `D >= B - A`. Such bounds are common in loop termination proofs where
    /// a counter `D` is bounded by the difference between two values.
    ///
    /// The invariant `D >= B - A` is equivalent to `D + A >= B` or `D + A - B >= 0`.
    pub(in crate::pdr::solver) fn discover_three_var_diff_bound_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            let has_facts = self.predicate_has_facts(pred.id);
            let has_incoming = self.has_any_incoming_inter_predicate_transitions(pred.id);

            // Skip predicates without facts AND without incoming transitions
            if !has_facts && !has_incoming {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Need at least 3 variables
            if canonical_vars.len() < 3 {
                continue;
            }

            // Extract three-variable difference bounds from init constraints (for fact preds)
            // or from entry edge constraints (for derived preds)
            let diff_bounds = if has_facts {
                self.extract_init_three_var_diff_bounds(pred.id)
            } else {
                self.extract_entry_edge_three_var_diff_bounds(pred.id)
            };

            if self.config.verbose && !diff_bounds.is_empty() {
                safe_eprintln!(
                    "PDR: Found {} three-var diff bounds for pred {}",
                    diff_bounds.len(),
                    pred.id.index()
                );
                for (v_d, v_b, v_a) in &diff_bounds {
                    safe_eprintln!("PDR:   {} >= {} - {}", v_d, v_b, v_a);
                }
            }

            // Check each candidate for preservation
            for (var_d_name, var_b_name, var_a_name) in &diff_bounds {
                if self.is_cancelled() {
                    return;
                }
                // Find variables in canonical list
                let var_d = canonical_vars.iter().find(|v| &v.name == var_d_name);
                let var_b = canonical_vars.iter().find(|v| &v.name == var_b_name);
                let var_a = canonical_vars.iter().find(|v| &v.name == var_a_name);

                let (var_d, var_b, var_a) = match (var_d, var_b, var_a) {
                    (Some(d), Some(b), Some(a)) => (d, b, a),
                    _ => continue,
                };

                // Check if the invariant is preserved by all transitions
                if !self.is_three_var_diff_bound_preserved(pred.id, var_d, var_b, var_a) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Three-var diff bound {} >= {} - {} is NOT preserved for pred {}",
                            var_d.name,
                            var_b.name,
                            var_a.name,
                            pred.id.index()
                        );
                    }
                    continue;
                }

                // Build the invariant: var_d >= var_b - var_a
                // Equivalent to: var_d + var_a >= var_b
                let diff_bound_invariant = ChcExpr::ge(
                    ChcExpr::add(ChcExpr::var(var_d.clone()), ChcExpr::var(var_a.clone())),
                    ChcExpr::var(var_b.clone()),
                );

                // Check if already known
                let already_known = self.frames.len() > 1
                    && self.frames[1]
                        .lemmas
                        .iter()
                        .any(|l| l.predicate == pred.id && l.formula == diff_bound_invariant);

                if already_known {
                    continue;
                }

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered three-var diff bound invariant for pred {}: {} >= {} - {} (i.e., {} + {} >= {})",
                        pred.id.index(),
                        var_d.name, var_b.name, var_a.name,
                        var_d.name, var_a.name, var_b.name
                    );
                }

                self.add_discovered_invariant(pred.id, diff_bound_invariant, 1);
            }
        }
    }

    /// Extract ALL inequality constraints from init and convert to canonical variables.
    pub(in crate::pdr::solver) fn extract_init_inequalities(
        &self,
        predicate: PredicateId,
    ) -> Vec<ChcExpr> {
        let mut inequalities = Vec::new();

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return inequalities,
        };

        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Build variable substitution from original names to canonical names
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        subst.push((v.clone(), ChcExpr::var(canon.clone())));
                    }
                    expr => {
                        // #2660: Expression head arg — map constituent vars
                        for v in expr.vars() {
                            if !subst.iter().any(|(sv, _)| sv.name == v.name) {
                                subst.push((v.clone(), ChcExpr::var(v.clone())));
                            }
                        }
                    }
                }
            }

            // Extract and convert all inequality constraints
            let conjuncts = constraint.collect_conjuncts();
            for conj in conjuncts {
                // Add inequality constraints (>=, <=, >, <) and their negations
                match &conj {
                    ChcExpr::Op(ChcOp::Ge | ChcOp::Le | ChcOp::Gt | ChcOp::Lt, _) => {
                        // Substitute to canonical variables
                        let canonical = conj.substitute(&subst);
                        inequalities.push(canonical);
                    }
                    // Handle (not (<= a b)) as (> a b) and (not (>= a b)) as (< a b)
                    // These are common in SMT-LIB encodings of strict inequalities
                    ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                        match args[0].as_ref() {
                            ChcExpr::Op(ChcOp::Le, inner_args) if inner_args.len() == 2 => {
                                // (not (<= a b)) => (> a b)
                                let gt = ChcExpr::gt(
                                    inner_args[0].as_ref().clone(),
                                    inner_args[1].as_ref().clone(),
                                );
                                let canonical = gt.substitute(&subst);
                                inequalities.push(canonical);
                            }
                            ChcExpr::Op(ChcOp::Ge, inner_args) if inner_args.len() == 2 => {
                                // (not (>= a b)) => (< a b)
                                let lt = ChcExpr::lt(
                                    inner_args[0].as_ref().clone(),
                                    inner_args[1].as_ref().clone(),
                                );
                                let canonical = lt.substitute(&subst);
                                inequalities.push(canonical);
                            }
                            ChcExpr::Op(ChcOp::Lt, inner_args) if inner_args.len() == 2 => {
                                // (not (< a b)) => (>= a b)
                                let ge = ChcExpr::ge(
                                    inner_args[0].as_ref().clone(),
                                    inner_args[1].as_ref().clone(),
                                );
                                let canonical = ge.substitute(&subst);
                                inequalities.push(canonical);
                            }
                            ChcExpr::Op(ChcOp::Gt, inner_args) if inner_args.len() == 2 => {
                                // (not (> a b)) => (<= a b)
                                let le = ChcExpr::le(
                                    inner_args[0].as_ref().clone(),
                                    inner_args[1].as_ref().clone(),
                                );
                                let canonical = le.substitute(&subst);
                                inequalities.push(canonical);
                            }
                            _ => {} // Not a simple negated inequality
                        }
                    }
                    _ => {} // Skip non-inequality constraints
                }
            }
        }

        inequalities
    }

    /// Extract three-variable difference bound patterns from init constraints.
    ///
    /// Looks for patterns like `(>= D (+ B (* (- 1) A)))` which represents `D >= B - A`.
    /// Also handles `(>= D (- B A))` directly.
    ///
    /// Returns Vec<(var_d_canonical, var_b_canonical, var_a_canonical)> for each found pattern.
    pub(in crate::pdr::solver) fn extract_init_three_var_diff_bounds(
        &self,
        predicate: PredicateId,
    ) -> Vec<(String, String, String)> {
        let mut bounds = Vec::new();

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return bounds,
        };

        for fact in self
            .problem
            .facts()
            .filter(|f| f.head.predicate_id() == Some(predicate))
        {
            let constraint = fact.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
            let head_args = match &fact.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Build variable map from original names to canonical names
            let mut var_map: FxHashMap<String, String> = FxHashMap::default();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        var_map.insert(v.name.clone(), canon.name.clone());
                    }
                    expr => {
                        // #2660: Expression head arg — map constituent vars to self
                        for v in expr.vars() {
                            var_map
                                .entry(v.name.clone())
                                .or_insert_with(|| v.name.clone());
                        }
                    }
                }
            }
            // Also identity mapping for canonical names
            for canon in &canonical_vars {
                var_map.insert(canon.name.clone(), canon.name.clone());
            }

            // Extract patterns from conjuncts
            let conjuncts = constraint.collect_conjuncts();
            for conj in &conjuncts {
                if let Some((var_d, var_b, var_a)) =
                    Self::extract_three_var_diff_bound_pattern(conj, &var_map)
                {
                    bounds.push((var_d, var_b, var_a));
                }
            }
        }

        bounds
    }

    /// Extract three-variable difference bounds from entry edges for derived predicates.
    ///
    /// For predicates without fact clauses (derived predicates), we extract diff bounds
    /// from the constraints of incoming transition clauses. For example, if:
    ///   FUN(B, A, E) ∧ (A >= E) ∧ (C = B) ∧ (D = 0) => SAD(C, D, E)
    /// Then SAD is entered with arg0 >= arg2 (since C = B = A and A >= E).
    ///
    /// This allows discovering bounds like `arg0 - arg1 >= arg2` which is true at entry
    /// because arg0 = B, arg1 = 0, arg2 = E and B >= E (from FUN invariant A = B).
    pub(in crate::pdr::solver) fn extract_entry_edge_three_var_diff_bounds(
        &self,
        predicate: PredicateId,
    ) -> Vec<(String, String, String)> {
        let mut bounds = Vec::new();

        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return bounds,
        };

        // Find incoming inter-predicate transition clauses
        for clause in self.problem.clauses() {
            let head_pred = match &clause.head {
                crate::ClauseHead::Predicate(p, _) if *p == predicate => p,
                _ => continue,
            };

            // Must have a body predicate that is different from head
            let is_entry = clause.body.predicates.iter().any(|(p, _)| *p != *head_pred);
            if !is_entry || clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                continue;
            }

            let constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Build variable map from original names to canonical names
            let mut var_map: FxHashMap<String, String> = FxHashMap::default();
            for (arg, canon) in head_args.iter().zip(canonical_vars.iter()) {
                match arg {
                    ChcExpr::Var(v) => {
                        var_map.insert(v.name.clone(), canon.name.clone());
                    }
                    expr => {
                        // #2660: Expression head arg — map constituent vars to self
                        for v in expr.vars() {
                            var_map
                                .entry(v.name.clone())
                                .or_insert_with(|| v.name.clone());
                        }
                    }
                }
            }
            // Also identity mapping for canonical names
            for canon in &canonical_vars {
                var_map.insert(canon.name.clone(), canon.name.clone());
            }

            // Track which canonical args are set to 0 (common pattern)
            let mut zero_args: FxHashSet<usize> = FxHashSet::default();
            for (i, arg) in head_args.iter().enumerate() {
                if matches!(arg, ChcExpr::Int(0)) {
                    zero_args.insert(i);
                }
            }

            // Extract explicit three-var diff bounds from the clause constraint
            let conjuncts = constraint.collect_conjuncts();
            for conj in &conjuncts {
                if let Some((var_d, var_b, var_a)) =
                    Self::extract_three_var_diff_bound_pattern(conj, &var_map)
                {
                    bounds.push((var_d, var_b, var_a));
                }
            }

            // Special case: if arg1 = 0 and there's a >= constraint involving head args,
            // we can derive a diff bound. E.g., if SAD(C, 0, E) with A >= E and C = B, A = B,
            // then C >= E which means arg0 - arg1 >= arg2 (since arg1 = 0).
            //
            // Look for patterns where head_arg_i >= head_arg_j in the constraint
            // and another head_arg_k = 0, then derive arg_i - arg_k >= arg_j.
            for conj in &conjuncts {
                if let ChcExpr::Op(ChcOp::Ge, args) = conj {
                    if args.len() != 2 {
                        continue;
                    }

                    // Try to find which canonical arg is on each side of the >=
                    let lhs_canon_idx = Self::find_canonical_index(&args[0], head_args);
                    let rhs_canon_idx = Self::find_canonical_index(&args[1], head_args);

                    let (Some(lhs_idx), Some(rhs_idx)) = (lhs_canon_idx, rhs_canon_idx) else {
                        continue;
                    };

                    // For each arg that is 0, we can form a diff bound
                    for &zero_idx in &zero_args {
                        if zero_idx == lhs_idx || zero_idx == rhs_idx {
                            continue;
                        }

                        // We have: arg[lhs_idx] >= arg[rhs_idx], and arg[zero_idx] = 0
                        // This gives: arg[lhs_idx] - arg[zero_idx] >= arg[rhs_idx]
                        let var_d = canonical_vars[lhs_idx].name.clone();
                        let var_a = canonical_vars[zero_idx].name.clone();
                        let var_b = canonical_vars[rhs_idx].name.clone();

                        // Only add if all are Int type
                        if matches!(canonical_vars[lhs_idx].sort, ChcSort::Int)
                            && matches!(canonical_vars[zero_idx].sort, ChcSort::Int)
                            && matches!(canonical_vars[rhs_idx].sort, ChcSort::Int)
                        {
                            bounds.push((var_d, var_b, var_a));
                        }
                    }
                }
            }
        }

        // Deduplicate bounds
        bounds.sort();
        bounds.dedup();
        bounds
    }
}
