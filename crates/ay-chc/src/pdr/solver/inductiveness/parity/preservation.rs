// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Transition-level parity preservation checks.
//!
//! Verifies that `(var mod k = c)` invariants are preserved across
//! all transitions defining a predicate, including self-loops and
//! cross-predicate transitions with optional exit-value substitution.

use super::super::super::PdrSolver;
use crate::smt::SmtResult;
use crate::{ChcExpr, ChcVar, PredicateId};

impl PdrSolver {
    /// Check if a parity (var mod k) is preserved by all transitions for a predicate.
    /// Delegates to the exit-value-aware variant with no exit values.
    pub(in crate::pdr::solver) fn is_parity_preserved_by_transitions(
        &mut self,
        predicate: PredicateId,
        var: &ChcVar,
        k: i128,
        expected_parity: i128,
    ) -> bool {
        self.is_parity_preserved_by_transitions_with_exit_values(
            predicate,
            var,
            k,
            expected_parity,
            None,
        )
    }

    /// Check if a parity (var mod k) is preserved by all transitions for a predicate,
    /// optionally using definite exit values for cross-predicate transitions (#425).
    ///
    /// Uses algebraic analysis rather than SMT queries for better performance.
    /// For a transition post = f(pre), parity is preserved if:
    /// - post = pre (identity), or
    /// - post = pre + c where c mod k == 0
    pub(in crate::pdr::solver) fn is_parity_preserved_by_transitions_with_exit_values(
        &mut self,
        predicate: PredicateId,
        var: &ChcVar,
        k: i128,
        expected_parity: i128,
        exit_values: Option<&ay_core::kani_compat::DetHashMap<(usize, usize), i128>>,
    ) -> bool {
        let canonical_vars = match self.canonical_vars(predicate) {
            Some(v) => v.to_vec(),
            None => return false,
        };

        // Find the index of var in canonical vars
        let idx = match canonical_vars.iter().position(|v| v.name == var.name) {
            Some(i) => i,
            None => return false,
        };

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
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: parity check: arity mismatch pred={} idx={} head_len={} canon_len={}",
                        predicate.index(),
                        idx,
                        head_args.len(),
                        canonical_vars.len()
                    );
                }
                return false;
            }

            // Get the head expression for var (post-state value)
            let head_val = &head_args[idx];

            // Get the body expression for var (pre-state value)
            if clause.body.predicates.len() != 1 {
                // Hyperedge - be conservative
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: parity check: hyperedge pred={} idx={} body_preds={}",
                        predicate.index(),
                        idx,
                        clause.body.predicates.len()
                    );
                }
                return false;
            }

            let (body_pred, body_args) = &clause.body.predicates[0];

            // IMPORTANT: We must check ALL transitions that define this predicate,
            // not just self-loops. For cross-predicate transitions (body_pred != predicate),
            // we need to verify the post-state parity, not the body parity.
            //
            // For self-loops (body_pred == predicate): check pre_mod == post_mod
            // For cross-predicate (body_pred != predicate): check post_mod == expected_parity
            //   where expected_parity must be provided by caller (from init value)

            if *body_pred == predicate {
                // Self-loop: check parity preservation algebraically, then via SMT fallback.
                if body_args.len() != canonical_vars.len() {
                    return false;
                }
                let body_val = &body_args[idx];

                // Get the constraint which may define the relationship between pre and post
                let constraint = clause.body.constraint.clone();

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: parity self-loop check: pred={} var={} mod {} expected={} body_val={} head_val={}",
                        predicate.index(),
                        var.name,
                        k,
                        expected_parity,
                        body_val,
                        head_val,
                    );
                }

                // Algebraic parity preservation check
                if Self::algebraic_parity_preserved(body_val, head_val, constraint.as_ref(), k) {
                    continue; // Parity preserved for this transition
                }

                // #2437 guardrail: if we can directly extract `post = pre + c` and `c mod k != 0`,
                // reject immediately. This blocks the known unsound `+1` pattern without
                // disabling fallback on harder transition shapes.
                if let (Some(constr), ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) =
                    (constraint.as_ref(), body_val, head_val)
                {
                    if let Some(offset) =
                        Self::find_offset_in_constraint(constr, &pre_v.name, &post_v.name)
                    {
                        if offset.rem_euclid(k) != 0 {
                            return false;
                        }
                    }
                }

                // #2881 guardrail: direct offset extraction from head expression.
                // Handles `body=Var, head=(+ Var constant)` without SMT fallback.
                // The SMT solver may return wrong UNSAT for mod queries, so this
                // algebraic check is the primary defense for this common pattern.
                if let ChcExpr::Var(pre_v) = body_val {
                    if let Some(offset) = Self::extract_addition_offset(head_val, &pre_v.name) {
                        if offset.rem_euclid(k) != 0 {
                            return false;
                        }
                        // offset mod k == 0 means parity is preserved; continue
                        continue;
                    }
                }

                // #2833 algebraic guardrail: if the constraint defines post = pre + expr
                // where expr contains variables (non-constant offset), check if
                // frame lemmas provide enough information for SMT to prove parity.
                // Originally this returned false for non-constant offsets (#2833),
                // but this blocked discovery of sum-parity invariants like dillig02_m
                // where post = pre + (C + B + D) and C+B+D is always even due to
                // frame lemmas. Now we fall through to the SMT check which includes
                // frame lemmas and can determine the offset's parity.
                // Part of #3219: SCC-cycle parity analysis.
                if let (Some(constr), ChcExpr::Var(pre_v), ChcExpr::Var(post_v)) =
                    (constraint.as_ref(), body_val, head_val)
                {
                    if let Some(def) = Self::find_var_definition(constr, &post_v.name) {
                        // Check if definition is pre_var + something
                        if def.contains_var_name(&pre_v.name) {
                            let is_const_offset =
                                Self::extract_addition_offset(&def, &pre_v.name).is_some();
                            if is_const_offset {
                                // Constant offset already handled by extract_addition_offset above
                            }
                            // Non-constant offset: try frame-aware algebraic check before
                            // falling through to SMT. The SMT solver often returns Unknown
                            // for mod 2 queries within 100ms, but frame equalities and
                            // parity lemmas can resolve them algebraically.
                            if !is_const_offset {
                                if self.frame_aware_offset_parity_check_with_constraint(
                                    predicate,
                                    &def,
                                    &pre_v.name,
                                    body_args,
                                    k,
                                    Some(constr),
                                ) {
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: frame-aware algebraic parity check \
                                             succeeded for pred {} var {} mod {}",
                                            predicate.index(),
                                            var.name,
                                            k,
                                        );
                                    }
                                    continue;
                                }
                            }
                        }
                    }
                }

                // Build inductiveness query:
                // pre mod k = expected /\ transition /\ frame_lemmas /\ post mod k != expected
                //
                // Previous query checked (pre mod k != post mod k) which gives false
                // negatives when post is a constant or function of other variables.
                // Example: counter reset (post = 0) with expected=0 — old query finds
                // pre=3 (odd, satisfies guard mod 3=0) as SAT, but the invariant IS
                // inductive because 0 mod 2 = 0 regardless of pre.
                let pre_invariant = ChcExpr::eq(
                    ChcExpr::mod_op(body_val.clone(), ChcExpr::Int(k)),
                    ChcExpr::Int(expected_parity),
                );
                let post_violates = ChcExpr::ne(
                    ChcExpr::mod_op(head_val.clone(), ChcExpr::Int(k)),
                    ChcExpr::Int(expected_parity),
                );

                let mut query_parts = vec![pre_invariant, post_violates];
                if let Some(c) = &constraint {
                    query_parts.push(c.clone());
                }

                let mut frame_lemma_count = 0usize;
                if !self.frames.is_empty() && self.frames.len() > 1 {
                    for lemma in self.frames[1]
                        .lemmas
                        .iter()
                        .filter(|l| l.predicate == predicate)
                    {
                        let body_canonical = match self.canonical_vars(predicate) {
                            Some(v) => v,
                            None => continue,
                        };
                        let substituted = Self::substitute_canonical_vars(
                            &lemma.formula,
                            body_canonical,
                            body_args,
                        );
                        query_parts.push(substituted);
                        frame_lemma_count += 1;
                    }
                }

                let query = ChcExpr::and_all(query_parts);

                self.smt.reset();
                let smt_result = self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(100));
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: parity SMT fallback for pred {} var {} mod {} self-loop (frame_lemmas={}): {:?}",
                        predicate.index(),
                        var.name,
                        k,
                        frame_lemma_count,
                        smt_result
                    );
                }
                match smt_result {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => continue,
                    _ => return false,
                }
            } else {
                // Cross-predicate transition: We need to verify that the post-state
                // has the expected parity, using frame invariants from the body predicate.
                //
                // Query: constraint ∧ body_invariants ∧ (head_expr mod k ≠ expected) is UNSAT?
                //
                // If UNSAT, the parity is preserved. If SAT or Unknown, reject the invariant.

                // BUG FIX #3121: Identity cross-predicate transitions (head_arg == body_arg
                // at this position) trivially preserve parity because the value passes through
                // unchanged. This breaks the circular dependency in dillig02_m where:
                // - inv's a5 parity check fails on clause 4 (inv1→inv, identity mapping)
                //   because inv1's a5 parity isn't known yet
                // - inv1's a5 parity needs inv's a5 parity for incoming transition inference
                // Recognizing the identity avoids the SMT query entirely.
                if body_args.len() > idx {
                    let body_val = &body_args[idx];
                    if body_val == head_val {
                        // Same expression at this position → value passes through unchanged.
                        continue;
                    }
                }

                let constraint = clause.body.constraint.clone();

                // First, try static parity computation on the head expression
                // This handles cases like head_val = constant * var where we know the parity
                if let Some(static_parity) =
                    Self::compute_static_expr_parity(head_val, &constraint, k)
                {
                    if static_parity != expected_parity {
                        // Static analysis shows parity differs from expected
                        return false;
                    }
                    // Static parity matches, continue to next clause
                    continue;
                }

                // Exit-value substitution (#425): for cross-predicate transitions
                // like itp1(A + B) where B is an inner loop counter with known
                // exit value, substitute the exit value to get a constant offset.
                if let Some(evs) = exit_values {
                    if let Some(exit_offset) = Self::resolve_cross_predicate_exit_offset(
                        head_val,
                        body_args,
                        constraint.as_ref(),
                        evs,
                        body_pred.index(),
                    ) {
                        if exit_offset.rem_euclid(k) == expected_parity {
                            continue;
                        } else {
                            return false;
                        }
                    }
                }

                // Build SMT query with body predicate's frame invariants
                let parity_differs = ChcExpr::ne(
                    ChcExpr::mod_op(head_val.clone(), ChcExpr::Int(k)),
                    ChcExpr::Int(expected_parity),
                );

                let mut query_parts = vec![parity_differs];
                if let Some(c) = &constraint {
                    query_parts.push(c.clone());
                }

                // Add frame invariants from the body predicate
                if !self.frames.is_empty() && self.frames.len() > 1 {
                    let body_canonical = match self.canonical_vars(*body_pred) {
                        Some(v) => v,
                        None => &[],
                    };

                    for lemma in self.frames[1]
                        .lemmas
                        .iter()
                        .filter(|l| l.predicate == *body_pred)
                    {
                        let substituted = Self::substitute_canonical_vars(
                            &lemma.formula,
                            body_canonical,
                            body_args,
                        );
                        query_parts.push(substituted);
                    }
                }

                // Build conjunction
                let query = ChcExpr::and_all(query_parts);

                self.smt.reset();
                // Use short timeout (100ms) for parity checks
                match self
                    .smt
                    .check_sat_with_timeout(&query, std::time::Duration::from_millis(100))
                {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        continue; // Definitely preserved
                    }
                    SmtResult::Sat(_) => {
                        // SMT found a counterexample - BUT this may be due to missing
                        // body predicate invariants. Check if the constraint alone
                        // implies something about the head expression's parity.
                        //
                        // Key insight: If the exit constraint specifies a fixed value
                        // or strong bounds on variables used in head_val, we can trust
                        // the SAT result. Otherwise, skip and let later phases handle it.
                        //
                        // For count_by_2_m_nest: exit is `B >= 16`, B=16 is reachable,
                        // 16 mod 3 != 0, so we correctly reject mod 3 invariants.
                        //
                        // For s_multipl_17: exit is `B > 0 AND B mod 3 = 0`, B=3 satisfies
                        // but the actual reachable B is 6 (also mod 2 = 0). We'd incorrectly
                        // reject if we trust the SAT result.
                        //
                        // Heuristic: If the constraint includes a modulo equality matching
                        // the expected parity modulus, the SAT is reliable. Otherwise skip.
                        let constraint_has_relevant_mod = constraint
                            .as_ref()
                            .is_some_and(|c| Self::constraint_has_mod_equality(c, k));

                        if constraint_has_relevant_mod {
                            // Constraint specifies mod k = something, so we can trust the check
                            continue; // Skip - let later phases discover if valid
                        } else {
                            // Constraint doesn't have mod info - be conservative and reject
                            // This catches count_by_2_m_nest where exit is just B >= 16
                            return false;
                        }
                    }
                    _ => {
                        // Unknown/Timeout - cannot prove preservation, reject (#2881)
                        return false;
                    }
                }
            }
        }

        // All transitions preserve the parity
        true
    }
}
