// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Three-variable difference bound pattern extraction and preservation checking.
//!
//! Pure pattern-matching helpers for recognizing `D >= B - A` in various AST
//! forms, plus the SMT-based inductive preservation check.

use super::*;

impl PdrSolver {
    /// Find which canonical argument index a variable expression corresponds to.
    ///
    /// Given an expression like `Var(A)` and head_args like `[Var(C), Var(D), Var(E)]`,
    /// if there's an equality constraint `C = A`, returns Some(0).
    pub(in crate::pdr::solver::invariant_discovery) fn find_canonical_index(
        expr: &ChcExpr,
        head_args: &[ChcExpr],
    ) -> Option<usize> {
        if let Some((idx, _)) = head_args.iter().enumerate().find(|(_, arg)| *arg == expr) {
            return Some(idx);
        }

        // Backward-compatible fallback for var-name matching if sorts differ.
        if let ChcExpr::Var(v) = expr {
            for (i, arg) in head_args.iter().enumerate() {
                if let ChcExpr::Var(a) = arg {
                    if a.name == v.name {
                        return Some(i);
                    }
                }
            }
        }
        None
    }

    /// Extract a three-variable difference bound pattern from a single constraint.
    ///
    /// Matches patterns:
    /// - `(>= D (+ B (* (- 1) A)))` -> `D >= B - A` -> Some((D, B, A))
    /// - `(>= D (+ B (* -1 A)))` -> `D >= B - A` -> Some((D, B, A))
    /// - `(>= D (- B A))` -> `D >= B - A` -> Some((D, B, A))
    /// - `(>= D (+ (* (- 1) A) B))` -> `D >= B - A` -> Some((D, B, A))
    pub(in crate::pdr::solver) fn extract_three_var_diff_bound_pattern(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> Option<(String, String, String)> {
        // Match (>= LHS RHS) where RHS is a difference of two variables
        if let ChcExpr::Op(ChcOp::Ge, args) = expr {
            if args.len() != 2 {
                return None;
            }

            // LHS must be a variable
            let var_d = match args[0].as_ref() {
                ChcExpr::Var(v) => var_map.get(&v.name)?.clone(),
                _ => return None,
            };

            // RHS must be a difference: var_b - var_a or var_b + (-1)*var_a
            let (var_b, var_a) = Self::extract_var_difference(&args[1], var_map)?;
            Some((var_d, var_b, var_a))
        } else {
            None
        }
    }

    /// Extract a variable difference pattern: var_b - var_a
    ///
    /// Matches:
    /// - `(- B A)` -> Some((B, A))
    /// - `(+ B (* (- 1) A))` -> Some((B, A))
    /// - `(+ B (* -1 A))` -> Some((B, A))
    /// - `(+ (* (- 1) A) B)` -> Some((B, A))
    pub(in crate::pdr::solver) fn extract_var_difference(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> Option<(String, String)> {
        match expr {
            // Direct subtraction: (- B A)
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                let var_b = match args[0].as_ref() {
                    ChcExpr::Var(v) => var_map.get(&v.name)?.clone(),
                    _ => return None,
                };
                let var_a = match args[1].as_ref() {
                    ChcExpr::Var(v) => var_map.get(&v.name)?.clone(),
                    _ => return None,
                };
                Some((var_b, var_a))
            }
            // Addition with negative coefficient: (+ B (* -1 A)) or (+ (* -1 A) B)
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
                // Try first arg as positive var, second as negative
                if let Some((var_b, var_a)) =
                    Self::try_extract_pos_neg_var_pair(&args[0], &args[1], var_map)
                {
                    return Some((var_b, var_a));
                }
                // Try second arg as positive var, first as negative
                if let Some((var_b, var_a)) =
                    Self::try_extract_pos_neg_var_pair(&args[1], &args[0], var_map)
                {
                    return Some((var_b, var_a));
                }
                None
            }
            _ => None,
        }
    }

    /// Try to extract (var_b, var_a) from (pos_expr, neg_expr) where
    /// pos_expr is a variable and neg_expr is (* -1 var) or (* (- 1) var).
    pub(in crate::pdr::solver) fn try_extract_pos_neg_var_pair(
        pos_expr: &ChcExpr,
        neg_expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> Option<(String, String)> {
        // pos_expr must be a variable
        let var_b = match pos_expr {
            ChcExpr::Var(v) => var_map.get(&v.name)?.clone(),
            _ => return None,
        };

        // neg_expr must be (* -1 var) or (* (- 1) var)
        let var_a = Self::extract_negated_var(neg_expr, var_map)?;

        Some((var_b, var_a))
    }

    /// Extract variable from a negation pattern: (* -1 var) or (* (- 1) var)
    pub(in crate::pdr::solver) fn extract_negated_var(
        expr: &ChcExpr,
        var_map: &FxHashMap<String, String>,
    ) -> Option<String> {
        if let ChcExpr::Op(ChcOp::Mul, args) = expr {
            if args.len() != 2 {
                return None;
            }

            // Check for coefficient -1 in various forms
            // Form 1: (* -1 var) or (* var -1) with literal Int(-1)
            if let (ChcExpr::Int(-1), ChcExpr::Var(v)) = (args[0].as_ref(), args[1].as_ref()) {
                return var_map.get(&v.name).cloned();
            }
            if let (ChcExpr::Var(v), ChcExpr::Int(-1)) = (args[0].as_ref(), args[1].as_ref()) {
                return var_map.get(&v.name).cloned();
            }

            // Form 2: (* (- 1) var) where (- 1) is Op(Sub, [Int(1)]) - unary subtraction
            if let ChcExpr::Op(ChcOp::Sub, sub_args) = args[0].as_ref() {
                if sub_args.len() == 1 && matches!(sub_args[0].as_ref(), ChcExpr::Int(1)) {
                    if let ChcExpr::Var(v) = args[1].as_ref() {
                        return var_map.get(&v.name).cloned();
                    }
                }
            }
            // Form 2b: (* var (- 1))
            if let ChcExpr::Op(ChcOp::Sub, sub_args) = args[1].as_ref() {
                if sub_args.len() == 1 && matches!(sub_args[0].as_ref(), ChcExpr::Int(1)) {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        return var_map.get(&v.name).cloned();
                    }
                }
            }

            // Form 3: (* (- 1) var) where (- 1) is Op(Neg, [Int(1)]) - unary negation
            if let ChcExpr::Op(ChcOp::Neg, neg_args) = args[0].as_ref() {
                if neg_args.len() == 1 && matches!(neg_args[0].as_ref(), ChcExpr::Int(1)) {
                    if let ChcExpr::Var(v) = args[1].as_ref() {
                        return var_map.get(&v.name).cloned();
                    }
                }
            }
            // Form 3b: (* var (- 1))
            if let ChcExpr::Op(ChcOp::Neg, neg_args) = args[1].as_ref() {
                if neg_args.len() == 1 && matches!(neg_args[0].as_ref(), ChcExpr::Int(1)) {
                    if let ChcExpr::Var(v) = args[0].as_ref() {
                        return var_map.get(&v.name).cloned();
                    }
                }
            }
        }
        None
    }

    /// Check if a three-variable difference bound is preserved by all transitions.
    ///
    /// For invariant `var_d >= var_b - var_a`, we check that for all transitions:
    /// `frame_invariants ∧ pre(var_d >= var_b - var_a) => post(var_d' >= var_b' - var_a')`
    ///
    /// Including frame invariants (e.g., relational invariants like B >= A) allows preservation
    /// to be proven when it depends on other invariants holding in the pre-state.
    pub(in crate::pdr::solver) fn is_three_var_diff_bound_preserved(
        &mut self,
        predicate: PredicateId,
        var_d: &ChcVar,
        var_b: &ChcVar,
        var_a: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Find indices
        let idx_d = canonical_vars.iter().position(|v| v.name == var_d.name);
        let idx_b = canonical_vars.iter().position(|v| v.name == var_b.name);
        let idx_a = canonical_vars.iter().position(|v| v.name == var_a.name);
        let (idx_d, idx_b, idx_a) = match (idx_d, idx_b, idx_a) {
            (Some(d), Some(b), Some(a)) => (d, b, a),
            _ => return false,
        };

        // Get existing frame invariants for this predicate (e.g., relational invariants like B >= A)
        let frame_invariants = self.get_frame_invariants_for_predicate(predicate);

        // Collect clause data first to avoid borrow conflicts
        struct ClauseData {
            body_d: ChcExpr,
            body_b: ChcExpr,
            body_a: ChcExpr,
            head_d: ChcExpr,
            head_b: ChcExpr,
            head_a: ChcExpr,
            transition_guard: ChcExpr,
            body_args: Vec<ChcExpr>,
        }
        let mut clause_data_list: Vec<ClauseData> = Vec::new();

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            // Get body predicate
            if clause.body.predicates.len() != 1 {
                return false; // Conservative for hyperedges
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            clause_data_list.push(ClauseData {
                body_d: body_args[idx_d].clone(),
                body_b: body_args[idx_b].clone(),
                body_a: body_args[idx_a].clone(),
                head_d: head_args[idx_d].clone(),
                head_b: head_args[idx_b].clone(),
                head_a: head_args[idx_a].clone(),
                transition_guard: clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true)),
                body_args: body_args.clone(),
            });
        }

        // If no self-loops were found, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }

        // Now process collected clause data
        for data in clause_data_list {
            // Substitute canonical variables in frame invariants with body args
            let mut combined_frame_invariants = ChcExpr::Bool(true);
            for inv in &frame_invariants {
                let substituted =
                    Self::substitute_canonical_vars(inv, &canonical_vars, &data.body_args);
                combined_frame_invariants = ChcExpr::and(combined_frame_invariants, substituted);
            }

            // Build pre-condition: body_d >= body_b - body_a
            // Equivalent to: body_d + body_a >= body_b
            let pre_cond = ChcExpr::ge(
                ChcExpr::add(data.body_d.clone(), data.body_a.clone()),
                data.body_b.clone(),
            );

            // Build post-condition: head_d >= head_b - head_a
            // Equivalent to: head_d + head_a >= head_b
            let post_cond = ChcExpr::ge(
                ChcExpr::add(data.head_d.clone(), data.head_a.clone()),
                data.head_b.clone(),
            );

            // Build implication: frame_invariants ∧ pre ∧ transition_guard => post
            // Check SAT of: frame_invariants ∧ pre ∧ transition_guard ∧ ¬post
            let query = ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::and(combined_frame_invariants.clone(), pre_cond.clone()),
                    data.transition_guard.clone(),
                ),
                ChcExpr::not(post_cond.clone()),
            );

            self.smt.reset();
            let timeout = std::time::Duration::from_millis(500);
            match self.smt.check_sat_with_timeout(&query, timeout) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Good - implication holds for this transition
                }
                SmtResult::Sat(_) => {
                    // Bad - found counterexample to preservation
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Three-var diff bound {} >= {} - {} NOT preserved by transition",
                            var_d.name,
                            var_b.name,
                            var_a.name
                        );
                    }
                    return false;
                }
                SmtResult::Unknown => {
                    // Conservative - assume not preserved
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Three-var diff bound {} >= {} - {} preservation check unknown",
                            var_d.name,
                            var_b.name,
                            var_a.name
                        );
                    }
                    return false;
                }
            }
        }

        true
    }
}
