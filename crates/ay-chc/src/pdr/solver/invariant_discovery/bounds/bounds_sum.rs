// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sum bound invariant discovery: invariants of the form A + B >= c and A + B <= c.
//!
//! Complements scaled difference bounds by finding invariants where two variables
//! have a bounded sum. Critical for benchmarks where two variables move in
//! opposite directions but maintain a sum invariant (e.g., s_mutants_21 needs
//! both A + B >= 0 and A + B <= 0 to establish A + B = 0).

use super::super::super::PdrSolver;
use super::{SUM_BOUND_CANDIDATES, SUM_UPPER_BOUND_CANDIDATES};
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcSort, ChcVar, PredicateId};

impl PdrSolver {
    /// Discover sum bounds (A + B >= c) for pairs of integer variables.
    ///
    /// This complements scaled_difference_bounds by finding invariants where two variables
    /// have a lower-bounded sum rather than a bounded difference. Critical for benchmarks
    /// where two variables move in opposite directions but maintain a sum invariant.
    ///
    /// Example: if x decrements and y increments each iteration, `x + y >= 0` may be invariant.
    pub(in crate::pdr::solver) fn discover_sum_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Only for predicates with fact clauses
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

            // #7048: Skip sum bounds for constant-constant pairs (same rationale as scaled-diff).
            let mut constant_args = self.detect_constant_arguments(pred.id);
            constant_args.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

            // Try sums A + B for pairs of integer variables
            for (i, var_a) in canonical_vars.iter().enumerate() {
                // Check cancellation to support solve_timeout / portfolio solving
                if self.is_cancelled() {
                    return;
                }
                if !matches!(var_a.sort, ChcSort::Int) {
                    continue;
                }

                for (j, var_b) in canonical_vars.iter().enumerate() {
                    if i >= j {
                        // Only check each pair once (i < j)
                        continue;
                    }
                    if !matches!(var_b.sort, ChcSort::Int) {
                        continue;
                    }
                    // #7048: Skip pairs where BOTH variables are constant.
                    if constant_args.contains(&i) && constant_args.contains(&j) {
                        continue;
                    }

                    // Find the TIGHTEST valid bound. Check from high to low.
                    // A higher c value means a tighter bound (A + B >= 2 implies A + B >= 1).
                    let mut tightest_valid: Option<i128> = None;
                    for c in SUM_BOUND_CANDIDATES {
                        // First check if A + B >= c holds at init
                        if !self.is_sum_bound_init_valid(pred.id, var_a, var_b, c) {
                            continue;
                        }

                        // Check if A + B >= c is preserved
                        if !self.is_sum_bound_preserved(pred.id, var_a, var_b, c) {
                            continue;
                        }

                        // Found the tightest valid bound - stop searching
                        tightest_valid = Some(c);
                        break;
                    }

                    // Only add the tightest bound if found
                    if let Some(c) = tightest_valid {
                        let sum_expr =
                            ChcExpr::add(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));
                        let bound_invariant = ChcExpr::ge(sum_expr, ChcExpr::Int(c));

                        // Check if already known
                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered sum bound for pred {}: {} + {} >= {}",
                                    pred.id.index(),
                                    var_a.name,
                                    var_b.name,
                                    c
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }
                }
            }
        }
    }

    /// Check if A + B >= c holds for all init states of the predicate.
    pub(in crate::pdr::solver) fn is_sum_bound_init_valid(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        // Check all fact clauses
        for clause in self.problem.clauses_defining(predicate) {
            // Only check fact clauses (no body predicates)
            if !clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let init_a = &head_args[var_a_idx];
            let init_b = &head_args[var_b_idx];

            // Check if A + B >= c under the fact constraint
            let sum_expr = ChcExpr::add(init_a.clone(), init_b.clone());
            let bound_violation = ChcExpr::lt(sum_expr, ChcExpr::Int(c));

            let fact_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(fact_constraint, bound_violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false, // Bound doesn't hold at init
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        true
    }

    /// Check if A + B >= c is preserved by all self-loop transitions.
    pub(in crate::pdr::solver) fn is_sum_bound_preserved(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        // Cache per-predicate invariants at level 1 to allow relative inductiveness checks.
        // This is needed for cases like dillig12 where `D = 2*C` is only preserved assuming
        // the already-learned equality `A = B` (see #1411).
        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        // Track whether we checked at least one self-loop clause (#1388).
        let mut checked_any_self_loop = false;

        // Check all self-loop clauses
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses
            if clause.body.predicates.is_empty() {
                continue;
            }

            // Only check self-loops for now
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip, only check self-loops for preservation.
                // If zero self-loops exist, we'll return false at the end (#1388).
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            // Get pre and post expressions for A and B
            let pre_a = &body_args[var_a_idx];
            let pre_b = &body_args[var_b_idx];
            let post_a = &head_args[var_a_idx];
            let post_b = &head_args[var_b_idx];

            // Pre-condition: A + B >= c
            let pre_sum = ChcExpr::add(pre_a.clone(), pre_b.clone());
            let pre_cond = ChcExpr::ge(pre_sum, ChcExpr::Int(c));

            // Post-condition violation: A' + B' < c
            let post_sum = ChcExpr::add(post_a.clone(), post_b.clone());
            let post_violation = ChcExpr::lt(post_sum, ChcExpr::Int(c));

            // Query: pre_cond AND f1(body_args) AND clause_constraint AND post_violation should be UNSAT
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // Build parts: pre_cond, clause_constraint, and optionally F1 on body
            let mut parts: Vec<ChcExpr> = vec![pre_cond, clause_constraint];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(base, post_violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Sum bound {} + {} >= {} NOT preserved",
                            var_a.name,
                            var_b.name,
                            c
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        // If zero self-loops were checked, cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        true
    }

    /// Discover sum upper bounds (A + B <= c) for pairs of integer variables.
    ///
    /// Complements `discover_sum_bounds` (which finds lower bounds A + B >= c) by
    /// finding upper bounds. Together, lower + upper bounds can establish sum
    /// equalities (e.g., A + B >= 0 AND A + B <= 0 implies A + B = 0).
    ///
    /// Critical for s_mutants_21 where the transition either does (+1,-1) or (-1,+1)
    /// preserving A + B = 0, but only the lower bound was discovered previously.
    pub(in crate::pdr::solver) fn discover_sum_upper_bounds(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let mut constant_args = self.detect_constant_arguments(pred.id);
            constant_args.extend(self.detect_frame_tight_bound_vars(pred.id).iter());

            for (i, var_a) in canonical_vars.iter().enumerate() {
                if self.is_cancelled() {
                    return;
                }
                if !matches!(var_a.sort, ChcSort::Int) {
                    continue;
                }

                for (j, var_b) in canonical_vars.iter().enumerate() {
                    if i >= j {
                        continue;
                    }
                    if !matches!(var_b.sort, ChcSort::Int) {
                        continue;
                    }
                    if constant_args.contains(&i) && constant_args.contains(&j) {
                        continue;
                    }

                    // Find the TIGHTEST valid upper bound. Check from low to high.
                    // A lower c value means a tighter bound (A + B <= -1 implies A + B <= 0).
                    let mut tightest_valid: Option<i128> = None;
                    for c in SUM_UPPER_BOUND_CANDIDATES {
                        if !self.is_sum_upper_bound_init_valid(pred.id, var_a, var_b, c) {
                            continue;
                        }

                        if !self.is_sum_upper_bound_preserved(pred.id, var_a, var_b, c) {
                            continue;
                        }

                        tightest_valid = Some(c);
                        break;
                    }

                    if let Some(c) = tightest_valid {
                        // A + B <= c is expressed as (not (> (+ A B) c)), i.e., (<= (+ A B) c)
                        let sum_expr =
                            ChcExpr::add(ChcExpr::var(var_a.clone()), ChcExpr::var(var_b.clone()));
                        let bound_invariant = ChcExpr::le(sum_expr, ChcExpr::Int(c));

                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered sum upper bound for pred {}: {} + {} <= {}",
                                    pred.id.index(),
                                    var_a.name,
                                    var_b.name,
                                    c
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }
                }
            }
        }
    }

    /// Check if A + B <= c holds for all init states of the predicate.
    pub(in crate::pdr::solver) fn is_sum_upper_bound_init_valid(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        for clause in self.problem.clauses_defining(predicate) {
            if !clause.body.predicates.is_empty() {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() {
                return false;
            }

            let init_a = &head_args[var_a_idx];
            let init_b = &head_args[var_b_idx];

            // Check if A + B <= c under the fact constraint, i.e., NOT (A + B > c)
            let sum_expr = ChcExpr::add(init_a.clone(), init_b.clone());
            let bound_violation = ChcExpr::gt(sum_expr, ChcExpr::Int(c));

            let fact_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(fact_constraint, bound_violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => return false,
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        true
    }

    /// Check if A + B <= c is preserved by all self-loop transitions.
    pub(in crate::pdr::solver) fn is_sum_upper_bound_preserved(
        &mut self,
        predicate: PredicateId,
        var_a: &ChcVar,
        var_b: &ChcVar,
        c: i128,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        let var_a_idx = canonical_vars.iter().position(|v| v.name == var_a.name);
        let var_b_idx = canonical_vars.iter().position(|v| v.name == var_b.name);

        let (var_a_idx, var_b_idx) = match (var_a_idx, var_b_idx) {
            (Some(a), Some(b)) => (a, b),
            _ => return false,
        };

        let f1_constraint = if self.frames.len() > 1 {
            self.cumulative_frame_constraint(1, predicate)
                .and_then(|f1| self.filter_f1_for_affine_check(&f1))
        } else {
            None
        };

        let mut checked_any_self_loop = false;

        for clause in self.problem.clauses_defining(predicate) {
            if clause.body.predicates.is_empty() {
                continue;
            }

            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                continue;
            }

            let head_args = match &clause.head {
                crate::ClauseHead::Predicate(_, args) => args,
                crate::ClauseHead::False => continue,
            };

            if head_args.len() != canonical_vars.len() || body_args.len() != canonical_vars.len() {
                return false;
            }

            checked_any_self_loop = true;

            let pre_a = &body_args[var_a_idx];
            let pre_b = &body_args[var_b_idx];
            let post_a = &head_args[var_a_idx];
            let post_b = &head_args[var_b_idx];

            // Pre-condition: A + B <= c
            let pre_sum = ChcExpr::add(pre_a.clone(), pre_b.clone());
            let pre_cond = ChcExpr::le(pre_sum, ChcExpr::Int(c));

            // Post-condition violation: A' + B' > c
            let post_sum = ChcExpr::add(post_a.clone(), post_b.clone());
            let post_violation = ChcExpr::gt(post_sum, ChcExpr::Int(c));

            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            let mut parts: Vec<ChcExpr> = vec![pre_cond, clause_constraint];
            if let Some(ref f1) = f1_constraint {
                if let Some(f1_on_body) = self.apply_to_args(predicate, f1, body_args) {
                    parts.push(f1_on_body);
                }
            }
            let base = parts
                .into_iter()
                .reduce(ChcExpr::and)
                .unwrap_or(ChcExpr::Bool(true));
            let query = ChcExpr::and(base, post_violation);

            self.smt.reset();
            match self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500))
            {
                SmtResult::Sat(_) => {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Sum upper bound {} + {} <= {} NOT preserved",
                            var_a.name,
                            var_b.name,
                            c
                        );
                    }
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    continue
                }
                SmtResult::Unknown => return false,
            }
        }

        if !checked_any_self_loop {
            return false;
        }
        true
    }
}
