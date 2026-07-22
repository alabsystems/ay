// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Definite exit-value analysis for nested loop invariant discovery.
//!
//! For self-loops with bounded counters (v' = v + c, guard: v < K, init: v0),
//! computes the exact exit value (first v >= bound). Enables parity discovery
//! for outer predicates by substituting definite exit values in cross-predicate
//! transitions. Novel technique — solves count_by_2_m_nest.

use super::super::PdrSolver;
use crate::pdr::frame::Lemma;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, HornClause, PredicateId};

impl PdrSolver {
    /// Compute definite exit values for all self-loop variables across all predicates.
    ///
    /// Returns a map from (predicate_id, var_idx) to the definite exit value.
    /// A definite exit value exists when:
    /// 1. The predicate has a single self-loop clause with constant increment
    /// 2. The self-loop guard is a simple upper bound (v < K or not(K <= v))
    /// 3. The init value is constant
    /// 4. The step divides evenly from init to bound (or overshoots to a unique value)
    pub(in crate::pdr::solver) fn compute_definite_exit_values(
        &self,
    ) -> ay_core::kani_compat::DetHashMap<(usize, usize), i128> {
        let mut exit_values: ay_core::kani_compat::DetHashMap<(usize, usize), i128> =
            Default::default();
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            if self.config.verbose {
                let n_clauses = self.problem.clauses_defining(pred.id).count();
                safe_eprintln!(
                    "PDR: exit-value: checking pred {} ({} vars, {} defining clauses)",
                    pred.id.index(),
                    canonical_vars.len(),
                    n_clauses,
                );
            }

            // Collect self-loop clauses for this predicate
            let self_loops: Vec<_> = self
                .problem
                .clauses_defining(pred.id)
                .filter(|c| c.body.predicates.len() == 1 && c.body.predicates[0].0 == pred.id)
                .collect();

            // Only handle the simple case: exactly one self-loop clause
            if self_loops.len() != 1 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: exit-value: pred {} has {} self-loops (need 1), skipping",
                        pred.id.index(),
                        self_loops.len(),
                    );
                }
                continue;
            }
            let clause = self_loops[0];

            let (_, body_args) = &clause.body.predicates[0];
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                continue;
            }

            let constraint = match &clause.body.constraint {
                Some(c) => c,
                None => continue,
            };

            // Collect entry clauses: non-self-loop clauses that define this predicate
            let entry_clauses: Vec<_> = self
                .problem
                .clauses_defining(pred.id)
                .filter(|c| {
                    if c.body.predicates.is_empty() {
                        return true; // fact clause
                    }
                    c.body.predicates.iter().all(|(bp, _)| *bp != pred.id)
                })
                .collect();

            // Get init values from standard mechanism
            let standard_init_values = self.get_init_values(pred.id);

            for (idx, var) in canonical_vars.iter().enumerate() {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                let body_val = &body_args[idx];
                let head_val = &head_args[idx];

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: exit-value: pred {} var {} idx={} body={} head={}",
                        pred.id.index(),
                        var.name,
                        idx,
                        body_val,
                        head_val,
                    );
                }

                // Extract constant step: head = body + c
                let step = match Self::extract_simple_offset(body_val, head_val) {
                    Some(c) if c > 0 => c,
                    _ => {
                        // Try resolving through constraint: body_val is Var(v),
                        // head_val is Var(w), constraint has w = v + c
                        if let (ChcExpr::Var(bv), ChcExpr::Var(hv)) = (body_val, head_val) {
                            if let Some(rhs) = Self::find_equality_rhs(constraint, &hv.name) {
                                match Self::extract_addition_offset(&rhs, &bv.name) {
                                    Some(c) if c > 0 => c,
                                    _ => continue,
                                }
                            } else {
                                continue;
                            }
                        } else {
                            continue;
                        }
                    }
                };

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: exit-value: pred {} var {} step={}",
                        pred.id.index(),
                        var.name,
                        step,
                    );
                }

                // Get init value for this variable.
                // Try standard init_values first, then look in entry clause constraints.
                let init_val = if let Some(bounds) = standard_init_values.get(&var.name) {
                    if bounds.min == bounds.max {
                        bounds.min
                    } else {
                        continue;
                    }
                } else {
                    // Extract init value from entry clause constraints.
                    match Self::extract_init_from_entry_clauses(
                        &entry_clauses,
                        idx,
                        &canonical_vars,
                    ) {
                        Some(v) => v,
                        None => continue,
                    }
                };

                // Extract upper bound from the self-loop guard
                let body_var_name = match body_val {
                    ChcExpr::Var(v) => &v.name,
                    _ => continue,
                };

                let bound = match Self::extract_strict_upper_bound(constraint, body_var_name) {
                    Some(b) => b,
                    None => continue,
                };

                // Compute definite exit value: smallest init_val + n*step >= bound
                if let Some(exit_val) = compute_definite_exit_value(init_val, step, bound) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Definite exit value for pred {} var {}: \
                             init={}, step={}, bound={}, exit={}",
                            pred.id.index(),
                            var.name,
                            init_val,
                            step,
                            bound,
                            exit_val,
                        );
                    }
                    exit_values.insert((pred.id.index(), idx), exit_val);
                }
            }
        }

        exit_values
    }

    /// Extract init value for a variable at a given index from entry clauses.
    ///
    /// Looks at non-self-loop clauses defining a predicate for direct equality
    /// constraints on the head argument at position `idx`.
    fn extract_init_from_entry_clauses(
        entry_clauses: &[&HornClause],
        idx: usize,
        canonical_vars: &[ChcVar],
    ) -> Option<i128> {
        // All entry clauses must agree on the same init value
        let mut init_val: Option<i128> = None;

        for clause in entry_clauses {
            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                crate::ClauseHead::False => continue,
            };

            if idx >= head_args.len() || head_args.len() != canonical_vars.len() {
                return None;
            }

            let constraint = clause.body.constraint.as_ref();

            // Case 1: head arg is a constant integer
            if let ChcExpr::Int(v) = &head_args[idx] {
                match init_val {
                    Some(prev) if prev != *v => return None,
                    Some(_) => {}
                    None => init_val = Some(*v),
                }
                continue;
            }

            // Case 2: head arg is a variable with an equality in the constraint
            if let ChcExpr::Var(hv) = &head_args[idx] {
                if let Some(c) = constraint {
                    if let Some(ChcExpr::Int(v)) = Self::find_equality_rhs(c, &hv.name) {
                        match init_val {
                            Some(prev) if prev != v => return None,
                            Some(_) => {}
                            None => init_val = Some(v),
                        }
                        continue;
                    }
                }
                return None;
            }

            return None;
        }

        init_val
    }

    /// Extract a strict upper bound on a variable from a constraint.
    ///
    /// Looks for patterns:
    /// - `not(<= K var)` → var < K (bound = K)
    /// - `(< var K)` → var < K (bound = K)
    /// - `not(>= var K)` → var < K (bound = K)
    ///
    /// Returns Some(K) if a strict upper bound is found.
    fn extract_strict_upper_bound(constraint: &ChcExpr, var_name: &str) -> Option<i128> {
        match constraint {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(b) = Self::extract_strict_upper_bound(arg, var_name) {
                        return Some(b);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                match args[0].as_ref() {
                    // not(<= K var) → not(K ≤ var) → var < K
                    ChcExpr::Op(ChcOp::Le, inner_args) if inner_args.len() == 2 => {
                        if let (ChcExpr::Int(k), ChcExpr::Var(v)) =
                            (inner_args[0].as_ref(), inner_args[1].as_ref())
                        {
                            if v.name == var_name {
                                return Some(*k);
                            }
                        }
                        None
                    }
                    // not(>= var K) → var < K
                    ChcExpr::Op(ChcOp::Ge, inner_args) if inner_args.len() == 2 => {
                        if let (ChcExpr::Var(v), ChcExpr::Int(k)) =
                            (inner_args[0].as_ref(), inner_args[1].as_ref())
                        {
                            if v.name == var_name {
                                return Some(*k);
                            }
                        }
                        None
                    }
                    _ => None,
                }
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                if let (ChcExpr::Var(v), ChcExpr::Int(k)) = (args[0].as_ref(), args[1].as_ref()) {
                    if v.name == var_name {
                        return Some(*k);
                    }
                }
                None
            }
            _ => None,
        }
    }

    /// Use exit-value information to determine if a cross-predicate transition
    /// preserves parity via exit-value substitution.
    ///
    /// Returns Some(effective_offset) if the head expression can be resolved to
    /// outer_var + exit_value, where exit_value is the definite exit value.
    pub(in crate::pdr::solver) fn resolve_cross_predicate_exit_offset(
        head_val: &ChcExpr,
        body_args: &[ChcExpr],
        constraint: Option<&ChcExpr>,
        exit_values: &ay_core::kani_compat::DetHashMap<(usize, usize), i128>,
        body_pred_idx: usize,
    ) -> Option<i128> {
        // Resolve head expression: if head is Var(C), look up C = expr in constraint
        let resolved_head = match head_val {
            ChcExpr::Var(hv) => {
                if let Some(c) = constraint {
                    Self::find_equality_rhs(c, &hv.name).unwrap_or_else(|| head_val.clone())
                } else {
                    head_val.clone()
                }
            }
            _ => head_val.clone(),
        };

        // Try pattern: resolved = var_a + var_b where one has exit value
        if let ChcExpr::Op(ChcOp::Add, args) = &resolved_head {
            if args.len() == 2 {
                for (a, b) in [(0, 1), (1, 0)] {
                    if let Some(exit_val) = Self::get_exit_value_for_expr(
                        &args[b],
                        body_args,
                        exit_values,
                        body_pred_idx,
                    ) {
                        if Self::is_body_var(&args[a], body_args) {
                            return Some(exit_val);
                        }
                    }
                }
            }
        }

        None
    }

    /// Check if an expression matches a body variable at some position.
    fn is_body_var(expr: &ChcExpr, body_args: &[ChcExpr]) -> bool {
        if let ChcExpr::Var(v) = expr {
            body_args.iter().any(|ba| {
                if let ChcExpr::Var(bv) = ba {
                    bv.name == v.name
                } else {
                    false
                }
            })
        } else {
            false
        }
    }

    /// Look up if an expression corresponds to a body variable with a definite exit value.
    fn get_exit_value_for_expr(
        expr: &ChcExpr,
        body_args: &[ChcExpr],
        exit_values: &ay_core::kani_compat::DetHashMap<(usize, usize), i128>,
        body_pred_idx: usize,
    ) -> Option<i128> {
        if let ChcExpr::Var(v) = expr {
            for (idx, ba) in body_args.iter().enumerate() {
                if let ChcExpr::Var(bv) = ba {
                    if bv.name == v.name {
                        return exit_values.get(&(body_pred_idx, idx)).copied();
                    }
                }
            }
        }
        None
    }

    /// Discover upper bounds via exit-value composition for cross-predicate cycles (#425).
    pub(in crate::pdr::solver) fn discover_composed_loop_bounds(
        &mut self,
        exit_values: &ay_core::kani_compat::DetHashMap<(usize, usize), i128>,
    ) {
        if exit_values.is_empty() {
            return;
        }
        let mut candidates: Vec<(PredicateId, ChcVar, i128)> = Vec::new();
        let predicates: Vec<_> = self.problem.predicates().to_vec();
        for pred in &predicates {
            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };
            let init_values = self.get_init_values(pred.id);
            for (idx, var) in canonical_vars.iter().enumerate() {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }
                let init_val = match init_values.get(&var.name) {
                    Some(b) if b.min == b.max => b.min,
                    _ => continue,
                };
                let using_clauses: Vec<_> = self.problem.clauses_using(pred.id).collect();
                for clause in &using_clauses {
                    if clause.body.predicates.len() != 1 {
                        continue;
                    }
                    let (body_pred, body_args) = &clause.body.predicates[0];
                    if *body_pred != pred.id {
                        continue;
                    }
                    let head_pred_id = match &clause.head {
                        crate::ClauseHead::Predicate(pid, _) => *pid,
                        crate::ClauseHead::False => continue,
                    };
                    if let Some(constraint_expr) = clause.body.constraint.as_ref() {
                        let body_var_name = match &body_args[idx] {
                            ChcExpr::Var(v) => v.name.clone(),
                            _ => continue,
                        };
                        let bound =
                            match Self::extract_strict_upper_bound(constraint_expr, &body_var_name)
                            {
                                Some(b) => b,
                                None => continue,
                            };
                        let ret_clauses: Vec<_> = self.problem.clauses_defining(pred.id).collect();
                        for ret_clause in &ret_clauses {
                            if ret_clause.body.predicates.len() != 1 {
                                continue;
                            }
                            let (ret_body_pred, ret_body_args) = &ret_clause.body.predicates[0];
                            if *ret_body_pred != head_pred_id {
                                continue;
                            }
                            let ret_head_args = match &ret_clause.head {
                                crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                                crate::ClauseHead::False => continue,
                            };
                            if idx >= ret_head_args.len() {
                                continue;
                            }
                            if let Some(exit_offset) = Self::resolve_cross_predicate_exit_offset(
                                &ret_head_args[idx],
                                ret_body_args,
                                ret_clause.body.constraint.as_ref(),
                                exit_values,
                                ret_body_pred.index(),
                            ) {
                                if let Some(composed_exit) =
                                    compute_definite_exit_value(init_val, exit_offset, bound)
                                {
                                    candidates.push((pred.id, var.clone(), composed_exit));
                                }
                            }
                        }
                    }
                }
            }
        }
        for (pred_id, var, composed_exit) in candidates {
            let bound_formula = ChcExpr::le(ChcExpr::var(var), ChcExpr::Int(composed_exit));
            self.add_lemma_to_frame(
                Lemma::new(pred_id, bound_formula, 1).with_algebraically_verified(true),
                1,
            );
        }
    }
}

/// Compute the definite exit value for a bounded counter loop.
///
/// Given: variable starts at `init_val`, increments by `step` each iteration,
/// loop continues while variable < `bound`.
///
/// Returns the value of the variable when the loop exits (first value >= bound).
fn compute_definite_exit_value(init_val: i128, step: i128, bound: i128) -> Option<i128> {
    if step <= 0 || bound <= init_val {
        return None;
    }
    let gap = bound.checked_sub(init_val)?;
    let n = if gap % step == 0 {
        gap / step
    } else {
        (gap / step).checked_add(1)?
    };
    let exit_val = init_val.checked_add(n.checked_mul(step)?)?;
    if exit_val >= bound {
        Some(exit_val)
    } else {
        None
    }
}
