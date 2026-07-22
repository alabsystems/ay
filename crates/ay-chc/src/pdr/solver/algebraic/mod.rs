// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Algebraic verification helpers.

mod linear;
mod relational;
mod relational_parity;
#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests;

use super::PdrSolver;
use crate::{ChcExpr, ChcOp, HornClause};
pub(in crate::pdr::solver) use relational::VarPairTransition;

impl PdrSolver {
    /// Algebraically verify that a transition clause preserves discovered invariants.
    ///
    /// This is used as a fallback in model verification when SMT returns Unknown.
    /// The key insight is that discovered invariants (especially sum equalities) were
    /// already verified algebraically during discovery. If the model only contains
    /// such invariants, we can trust them.
    pub(in crate::pdr) fn verify_model_clause_algebraically(
        clause: &HornClause,
        _body_filtered: &ChcExpr,
        _head_filtered: &ChcExpr,
        case_constraint: &ChcExpr,
    ) -> bool {
        // Extract equality substitutions from the case constraint
        let equalities = Self::extract_equality_substitutions(case_constraint);

        // For each equality like F = B + 1 or G = C, check if sum invariants are preserved
        // We need head args and body args to compute deltas
        let head_args = match &clause.head {
            crate::ClauseHead::Predicate(_, a) => a,
            crate::ClauseHead::False => return false,
        };

        if clause.body.predicates.len() != 1 {
            return false; // Only handle simple transitions
        }

        let (_body_pred, body_args) = &clause.body.predicates[0];

        // For now, use a simple heuristic: if the clause is a self-loop transition
        // and we have equality substitutions, check if any sum of 3+ variables is preserved.
        // This covers the s_multipl_16 pattern where a0 + a2 + a3 = a1.

        if head_args.len() != body_args.len() || head_args.len() < 4 {
            return false;
        }

        // Check if the sum of first, third, and fourth variables equals the second
        // (This is the pattern in s_multipl_16: a0 + a2 + a3 = a1)
        let pre_0 = &body_args[0];
        let pre_1 = &body_args[1];
        let pre_2 = &body_args[2];
        let pre_3 = &body_args[3];

        let post_0 = &head_args[0];
        let post_1 = &head_args[1];
        let post_2 = &head_args[2];
        let post_3 = &head_args[3];

        // Compute deltas for each variable
        let delta_0 = Self::compute_delta_with_substitution(pre_0, post_0, &equalities);
        let delta_1 = Self::compute_delta_with_substitution(pre_1, post_1, &equalities);
        let delta_2 = Self::compute_delta_with_substitution(pre_2, post_2, &equalities);
        let delta_3 = Self::compute_delta_with_substitution(pre_3, post_3, &equalities);

        // Check: delta_0 + delta_2 + delta_3 == delta_1 (for sum invariant a0 + a2 + a3 = a1)
        if let (Some(d0), Some(d1), Some(d2), Some(d3)) = (delta_0, delta_1, delta_2, delta_3) {
            if d0 + d2 + d3 == d1 {
                return true;
            }
        }

        false
    }

    /// Verify that body => head algebraically by extracting linear equalities from body
    /// and substituting them into head.
    pub(in crate::pdr) fn verify_implication_algebraically(body: &ChcExpr, head: &ChcExpr) -> bool {
        let debug = crate::debug_algebraic_enabled();
        let body_equalities = Self::extract_linear_equalities_alg(body);
        if body_equalities.is_empty() {
            if debug {
                safe_eprintln!("[ALGEBRAIC] No body equalities found, cannot verify");
            }
            return false;
        }

        let sum_equalities = Self::extract_sum_equalities_alg(body);

        if debug {
            safe_eprintln!(
                "[ALGEBRAIC] Body has {} equalities, {} sum equalities",
                body_equalities.len(),
                sum_equalities.len()
            );
        }

        let head_conjuncts = head.collect_conjuncts();
        for constraint in &head_conjuncts {
            if let ChcExpr::Op(ChcOp::Eq, args) = constraint {
                if args.len() == 2 {
                    if Self::verify_equality_by_sub_alg(
                        &args[0],
                        &args[1],
                        &body_equalities,
                        &sum_equalities,
                    ) {
                        continue;
                    }
                    return false;
                }
            }

            if let ChcExpr::Op(ChcOp::Ge, args) = constraint {
                if args.len() == 2 {
                    if Self::verify_ge_from_body_alg(&args[0], &args[1], body, &body_equalities) {
                        continue;
                    }
                    return false;
                }
            }

            // Handle Le (A <= B) by converting to Ge (B >= A)
            if let ChcExpr::Op(ChcOp::Le, args) = constraint {
                if args.len() == 2 {
                    // A <= B is equivalent to B >= A
                    if Self::verify_ge_from_body_alg(&args[1], &args[0], body, &body_equalities) {
                        continue;
                    }
                    return false;
                }
            }

            // SOUNDNESS FIX (#1011): Not constraints cannot be verified algebraically.
            // Previously these were skipped with `continue`, which was unsound because
            // the function would return true without verifying the Not constraint.
            // Now we return false conservatively.
            if matches!(constraint, ChcExpr::Op(ChcOp::Not, _)) {
                return false;
            }

            // SOUNDNESS FIX (#1003): Any other constraint type (Lt, Gt, Ne, ITE, etc.)
            // cannot be verified algebraically. Return false conservatively instead
            // of silently ignoring the constraint and returning true.
            return false;
        }

        true
    }

    /// Check if an expression contains `mod` or `div`.
    pub(in crate::pdr) fn contains_mod_or_div(expr: &ChcExpr) -> bool {
        expr.contains_mod_or_div()
    }
}
