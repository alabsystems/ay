// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sum preservation checking for PDR invariant discovery.
//!
//! Verifies that sum invariants (e.g., x + y = constant) are preserved
//! by all transition clauses. Includes both algebraic verification and
//! SMT-based fallback with OR-case splitting.

use super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcOp, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Verify that a triple sum invariant is preserved by computing symbolic deltas.
    ///
    /// For the invariant (i + j + k = l) to be preserved:
    ///   (post_i - pre_i) + (post_j - pre_j) + (post_k - pre_k) = (post_l - pre_l)
    ///
    /// This function extracts equalities from the constraint (e.g., F = B + 1, G = C)
    /// and substitutes them to compute deltas. Returns true if the sum of deltas equals
    /// the target delta.
    #[allow(clippy::too_many_arguments)]
    pub(in crate::pdr::solver) fn verify_triple_sum_algebraically(
        pre_i: &ChcExpr,
        pre_j: &ChcExpr,
        pre_k: &ChcExpr,
        pre_l: &ChcExpr,
        post_i: &ChcExpr,
        post_j: &ChcExpr,
        post_k: &ChcExpr,
        post_l: &ChcExpr,
        constraint: &ChcExpr,
    ) -> bool {
        // Extract equalities from the constraint
        let equalities = Self::extract_equality_substitutions(constraint);

        // Compute deltas with substitution
        let delta_i = Self::compute_delta_with_substitution(pre_i, post_i, &equalities);
        let delta_j = Self::compute_delta_with_substitution(pre_j, post_j, &equalities);
        let delta_k = Self::compute_delta_with_substitution(pre_k, post_k, &equalities);
        let delta_l = Self::compute_delta_with_substitution(pre_l, post_l, &equalities);

        // Check if all deltas were computed successfully
        let (delta_i, delta_j, delta_k, delta_l) = match (delta_i, delta_j, delta_k, delta_l) {
            (Some(di), Some(dj), Some(dk), Some(dl)) => (di, dj, dk, dl),
            _ => return false, // Could not compute deltas symbolically
        };

        // Check: delta_i + delta_j + delta_k == delta_l
        delta_i + delta_j + delta_k == delta_l
    }

    /// Extract equality substitutions from a constraint.
    ///
    /// Returns a map from variable names to their delta offsets from other variables.
    /// For example, if constraint contains (= F (+ 1 B)), we record F -> (B, 1) meaning F = B + 1.
    pub(in crate::pdr::solver) fn extract_equality_substitutions(
        constraint: &ChcExpr,
    ) -> FxHashMap<String, (String, i128)> {
        let mut subs = FxHashMap::default();

        // Collect all conjuncts
        let conjuncts = constraint.collect_conjuncts();

        for conjunct in conjuncts {
            // Look for equalities: (= var1 var2) or (= var (+ n other)) or (= var (+ other n))
            if let ChcExpr::Op(ChcOp::Eq, args) = &conjunct {
                if args.len() == 2 {
                    Self::extract_single_equality(&args[0], &args[1], &mut subs);
                    Self::extract_single_equality(&args[1], &args[0], &mut subs);
                }
            }
        }

        subs
    }

    /// Extract a single equality from two expressions.
    /// If lhs is a variable and rhs is (var) or (var + const) or (const + var), record the substitution.
    pub(in crate::pdr::solver) fn extract_single_equality(
        lhs: &ChcExpr,
        rhs: &ChcExpr,
        subs: &mut FxHashMap<String, (String, i128)>,
    ) {
        let lhs_var = match lhs {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return,
        };

        // Case 1: rhs is a variable (F = B means delta_F = delta_B)
        if let ChcExpr::Var(v) = rhs {
            subs.insert(lhs_var, (v.name.clone(), 0));
            return;
        }

        // Case 2: rhs is (+ var const) or (+ const var)
        if let ChcExpr::Op(ChcOp::Add, add_args) = rhs {
            if add_args.len() == 2 {
                let (var_name, offset) = Self::extract_var_and_offset(&add_args[0], &add_args[1]);
                if let Some((name, off)) = var_name.zip(offset) {
                    subs.insert(lhs_var, (name, off));
                    return;
                }
            }
        }

        // Case 3: rhs is (- var const) which means var - const
        if let ChcExpr::Op(ChcOp::Sub, sub_args) = rhs {
            if sub_args.len() == 2 {
                if let (ChcExpr::Var(v), ChcExpr::Int(n)) =
                    (sub_args[0].as_ref(), sub_args[1].as_ref())
                {
                    subs.insert(lhs_var, (v.name.clone(), -*n));
                }
            }
        }
    }

    /// Compute the delta (post - pre) for a variable with substitution.
    ///
    /// Returns Some(delta) if the delta can be computed as a constant offset.
    /// For example, if pre = A and post = (A - 1), returns Some(-1).
    pub(in crate::pdr::solver) fn compute_delta_with_substitution(
        pre: &ChcExpr,
        post: &ChcExpr,
        subs: &FxHashMap<String, (String, i128)>,
    ) -> Option<i128> {
        // Get the base variable name from pre (should be a simple variable)
        let pre_var = match pre {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return None,
        };

        // Analyze post to compute delta
        let (post_var, post_offset) = Self::decompose_linear_expr(post)?;

        // Apply substitution if post_var is in subs
        let (final_var, extra_offset) = if let Some((subst_var, subst_offset)) = subs.get(&post_var)
        {
            (subst_var.clone(), *subst_offset)
        } else {
            (post_var, 0)
        };

        // If final_var == pre_var, then delta = post_offset + extra_offset
        if final_var == pre_var {
            Some(post_offset + extra_offset)
        } else {
            // Can't compute delta - variables don't match
            None
        }
    }

    /// Check if the sum of two canonical variables is algebraically preserved by all transitions.
    ///
    /// For a sum to be preserved: if pre-state has (x, y) and post-state has (x', y'),
    /// then x' + y' = x + y must hold given the transition constraints.
    ///
    /// Example (preserved): x' = x + 1, y' = y - 1 => x' + y' = x + y
    /// Example (NOT preserved): a' = b, b' = a + b => a' + b' = b + (a+b) = a + 2b ≠ a + b
    pub(in crate::pdr::solver) fn is_sum_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var_i: &ChcVar,
        var_j: &ChcVar,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the indices of var_i and var_j in canonical vars
        let idx_i = canonical_vars.iter().position(|v| v.name == var_i.name);
        let idx_j = canonical_vars.iter().position(|v| v.name == var_j.name);
        let (idx_i, idx_j) = match (idx_i, idx_j) {
            (Some(i), Some(j)) => (i, j),
            _ => return false,
        };

        // Track whether we checked at least one self-loop clause.
        // If zero self-loops exist, we cannot claim preservation vacuously (#1388).
        let mut checked_any_self_loop = false;

        // Check all transition clauses that define this predicate
        for clause in self.problem.clauses_defining(predicate) {
            // Skip fact clauses (no body predicates)
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

            // Get the head expressions for var_i and var_j (post-state values)
            let head_i = &head_args[idx_i];
            let head_j = &head_args[idx_j];

            // Get the body expressions for var_i and var_j (pre-state values)
            // For single-predicate body, find the mapping
            if clause.body.predicates.len() != 1 {
                // Hyperedge - be conservative
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];
            if *body_pred != predicate {
                // Inter-predicate transition: skip this clause but don't return false.
                // We only care about self-loops for preservation. If no self-loops
                // exist, we'll detect that at the end (#1388 fix).
                continue;
            }
            if body_args.len() != canonical_vars.len() {
                return false;
            }

            // This is a self-loop clause - mark that we're checking at least one
            checked_any_self_loop = true;

            let body_i = &body_args[idx_i];
            let body_j = &body_args[idx_j];

            // Check: head_i + head_j = body_i + body_j given the clause constraint
            let clause_constraint = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));

            // First try algebraic verification: if we can substitute definitions
            // and prove head_i + head_j = body_i + body_j without SMT, do that.
            // This handles OR constraints that cause SMT to return Unknown.
            if Self::sum_algebraically_preserved(head_i, head_j, body_i, body_j, &clause_constraint)
            {
                continue;
            }

            let pre_sum = ChcExpr::add(body_i.clone(), body_j.clone());
            let post_sum = ChcExpr::add(head_i.clone(), head_j.clone());
            let sum_differs = ChcExpr::ne(pre_sum.clone(), post_sum.clone());

            // Try SMT query: constraint AND (pre_sum != post_sum)
            // If SAT, the sum is NOT preserved; if UNSAT, it IS preserved
            let query = ChcExpr::and(clause_constraint.clone(), sum_differs.clone());

            self.smt.reset();
            let result = self
                .smt
                .check_sat_with_timeout(&query, std::time::Duration::from_millis(500));

            match result {
                SmtResult::Sat(_) => {
                    // Sum is NOT preserved by this transition
                    return false;
                }
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                    // Sum IS preserved by this transition
                    continue;
                }
                SmtResult::Unknown => {
                    // Try case split: if constraint has OR at top level, check each case
                    if let Some(or_cases) = Self::extract_or_cases(&clause_constraint) {
                        if or_cases.len() > 1 {
                            let mut all_cases_unsat = true;
                            for case in &or_cases {
                                let case_query = ChcExpr::and(case.clone(), sum_differs.clone());
                                self.smt.reset();
                                let case_result = self.smt.check_sat_with_timeout(
                                    &case_query,
                                    std::time::Duration::from_millis(500),
                                );

                                match case_result {
                                    SmtResult::Sat(_) | SmtResult::Unknown => {
                                        all_cases_unsat = false;
                                        break;
                                    }
                                    SmtResult::Unsat
                                    | SmtResult::UnsatWithCore(_)
                                    | SmtResult::UnsatWithFarkas(_) => {
                                        continue;
                                    }
                                }
                            }

                            if all_cases_unsat {
                                continue;
                            }
                        }
                    }

                    // Can't verify - be conservative
                    return false;
                }
            }
        }

        // All self-loop transitions preserve the sum.
        // But if zero self-loops were checked, we cannot claim preservation vacuously (#1388).
        if !checked_any_self_loop {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Sum ({} + {}) is algebraically preserved by all transitions",
                var_i.name,
                var_j.name
            );
        }
        true
    }

    /// Algebraically verify that head_i + head_j = body_i + body_j given the constraint.
    ///
    /// This handles constraints with OR branches where each branch defines head vars
    /// in terms of body vars with offsets. For example:
    /// - (D = A+1 AND E = B-1) OR (D = A-1 AND E = B+1)
    /// - In both cases: D + E = A + B (algebraically verifiable)
    ///
    /// Also handles cases with intermediate variables:
    /// - D = B + F, E = C - F => D + E = B + C (F cancels out)
    ///
    /// Returns true if sum is preserved in all cases, false if we can't verify.
    pub(in crate::pdr::solver) fn sum_algebraically_preserved(
        head_i: &ChcExpr,
        head_j: &ChcExpr,
        body_i: &ChcExpr,
        body_j: &ChcExpr,
        constraint: &ChcExpr,
    ) -> bool {
        // Get variable names for head (post-state)
        let head_i_var = match head_i {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return false,
        };
        let head_j_var = match head_j {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return false,
        };

        // Get variable names for body (pre-state)
        let body_i_var = match body_i {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return false,
        };
        let body_j_var = match body_j {
            ChcExpr::Var(v) => v.name.clone(),
            _ => return false,
        };

        // Extract OR cases from constraint
        let cases = if let Some(cases) = Self::extract_or_cases(constraint) {
            cases
        } else {
            // No OR, treat whole constraint as single case
            vec![constraint.clone()]
        };

        // For each case, extract definitions and verify algebraically
        for case in &cases {
            // Extract definition of head_i: head_i = body_var + offset
            let def_i = Self::extract_var_linear_def(case, &head_i_var);
            let def_j = Self::extract_var_linear_def(case, &head_j_var);

            match (def_i, def_j) {
                (Some((base_i, offset_i)), Some((base_j, offset_j))) => {
                    // head_i = base_i + offset_i
                    // head_j = base_j + offset_j
                    // head_i + head_j = base_i + base_j + offset_i + offset_j
                    // For sum preservation: base_i + base_j = body_i + body_j (modulo renaming)
                    // and offset_i + offset_j = 0

                    // Check that bases match body vars (possibly in either order)
                    let bases_match = (base_i == body_i_var && base_j == body_j_var)
                        || (base_i == body_j_var && base_j == body_i_var);

                    if !bases_match {
                        return false;
                    }

                    // Check that offsets cancel out
                    if offset_i + offset_j != 0 {
                        return false;
                    }

                    // This case preserves the sum
                }
                _ => {
                    // Try extended form with variable terms: head_i = base_i + term, head_j = base_j - term
                    // where term is a variable expression that cancels out
                    let ext_def_i = Self::extract_var_linear_def_extended(case, &head_i_var);
                    let ext_def_j = Self::extract_var_linear_def_extended(case, &head_j_var);

                    match (ext_def_i, ext_def_j) {
                        (Some((base_i, term_i)), Some((base_j, term_j))) => {
                            // Check that bases match body vars
                            let bases_match = (base_i == body_i_var && base_j == body_j_var)
                                || (base_i == body_j_var && base_j == body_i_var);

                            if !bases_match {
                                return false;
                            }

                            // Check that terms cancel out (term_i + term_j = 0)
                            // term_i and term_j are (var_name, coefficient) pairs
                            // They cancel if same variable with opposite coefficients
                            let terms_cancel = match (&term_i, &term_j) {
                                (Some((var_i, coef_i)), Some((var_j, coef_j))) => {
                                    var_i == var_j && coef_i + coef_j == 0
                                }
                                (None, None) => true, // No variable terms, both are just base vars
                                _ => false,
                            };

                            if !terms_cancel {
                                return false;
                            }

                            // This case preserves the sum
                        }
                        _ => {
                            // Couldn't extract definitions
                            return false;
                        }
                    }
                }
            }
        }

        // All cases preserve the sum
        true
    }
}
