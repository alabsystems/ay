// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! When a Safe-model verifier may use `PdrSolver::new`'s solve-time clause
//! rewrites without weakening the original-clause check.

use super::*;

impl PortfolioSolver {
    /// Whether the solve-time rewrites that `PdrSolver::new` applies unless
    /// `preserve_original_clauses` is set are EXACT for `model` on
    /// `original_problem`, i.e. checking `model` on the rewritten clauses
    /// discharges precisely the obligations of the original clauses.
    ///
    /// - OR / ITE case splits are exact for every model: an original clause
    ///   becomes clauses whose conjunction is equivalent to it
    ///   (`B ∧ (a ∨ b) → H` ≡ `(B ∧ a → H) ∧ (B ∧ b → H)`;
    ///   `φ[ite(c,t,e)] → H` ≡ `(c ∧ φ[t] → H) ∧ (¬c ∧ φ[e] → H)`; clause
    ///   expressions carry no binders). Array scalarization is off in every
    ///   validator through `disable_array_scalarization`.
    /// - Nullary-fail expansion replaces each defining clause `B_i → P` of a
    ///   nullary query predicate `P` (a query `P ∧ φ → false`) by the query
    ///   `B_i → false`, and drops the `P` queries and the `P`-headed clauses.
    ///   With `model(P) = false` the dropped obligation `B_i[model] → model(P)`
    ///   is the added one verbatim (same body, same interpretations), and a
    ///   dropped query `model(P) ∧ φ → false` is valid. For any other
    ///   interpretation the rewrite loses obligations: `error = true` passes
    ///   the expanded problem but violates the original `error → false`
    ///   (f40f8c9d8, `nullary_query_tests`).
    ///
    /// So the rewrites are exact iff every predicate the expansion would
    /// eliminate is interpreted as the literal `false`. Anything else
    /// (including a missing interpretation or an equivalent-but-different
    /// formula) keeps the original clauses.
    pub(super) fn solve_time_rewrites_exact_for_model(&self, model: &InvariantModel) -> bool {
        self.original_problem
            .nullary_fail_query_clauses()
            .all(|(pred, _)| {
                model
                    .get(&pred)
                    .is_some_and(|interp| interp.formula == ChcExpr::Bool(false))
            })
    }
}
