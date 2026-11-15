// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The closed-interpretation check every model verification runs first.

use super::*;

impl PdrSolver {
    /// Reject ill-formed models whose interpretations mention FREE variables.
    ///
    /// SOUNDNESS: An invariant interpretation must be closed over its binder
    /// vars (`interp.vars`). If the formula references other variables, the
    /// substitution performed by `apply_interp_to_args` leaves them free in
    /// the verification query, where they are CAPTURED by same-named
    /// clause-local variables. Clause constraints can then contradict the
    /// captured conjuncts, making consecution checks vacuously UNSAT and
    /// letting a non-invariant "pass" full validation (022c-horn_000
    /// false-SAT: synthesized `INV1 := ¬(... ∧ (= G H) ∧ (= I J))` with free
    /// G/H/I/J was validated against clauses whose own G/H/I/J satisfied
    /// `(>= (- G H) 1)`, discharging every check).
    ///
    /// Returns `true` (reject) when any interpretation used by the problem
    /// has free variables.
    pub(in crate::pdr::verification) fn model_has_free_interpretation_vars(
        &self,
        model: &InvariantModel,
    ) -> bool {
        for pred in self.problem.predicates() {
            let Some(interp) = model.get(&pred.id) else {
                continue;
            };
            let param_names: ay_core::kani_compat::DetHashSet<&str> =
                interp.vars.iter().map(|v| v.name.as_str()).collect();
            if let Some(free_var) = interp
                .formula
                .vars()
                .iter()
                .find(|v| !param_names.contains(v.name.as_str()))
            {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: verify_model: rejecting ill-formed model — pred {} interpretation \
                         has free variable `{}` not among its binder vars (capture-unsound)",
                        pred.id.index(),
                        free_var.name
                    );
                }
                tracing::warn!(
                    pred = pred.id.index(),
                    free_var = %free_var.name,
                    "verify_model: rejecting model with free interpretation variable \
                     (substitution capture would make clause checks vacuous)"
                );
                return true;
            }
        }
        false
    }

    /// Whether every interpretation present in `model` uses exactly
    /// `problem`'s predicate signatures (binder count and sort, positionally).
    /// Missing interpretations do not decide the vocabulary; the ordinary
    /// completeness check in the selected verifier still rejects them.
    pub(super) fn model_matches_problem_signature(
        model: &InvariantModel,
        problem: &crate::ChcProblem,
    ) -> bool {
        let mut any_present = false;
        for (pred_id, interp) in model.iter() {
            let Some(pred) = problem.get_predicate(*pred_id) else {
                return false;
            };
            any_present = true;
            if interp.vars.len() != pred.arg_sorts.len()
                || interp
                    .vars
                    .iter()
                    .zip(pred.arg_sorts.iter())
                    .any(|(var, sort)| &var.sort != sort)
            {
                return false;
            }
        }
        any_present
    }
}
