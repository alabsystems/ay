// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Budget policy for the adaptive solver's algebraic invariant pre-stage.

use crate::classifier::{ProblemClass, ProblemFeatures};
use std::time::Duration;

/// Wall-clock cap for the algebraic invariant pre-strategy (#8753).
///
/// Algebraic synthesis is advertised as `<100ms`, but the SMT validation
/// phase could previously burn the full CHC wall clock on NIA/LRA dual
/// simplex loops (`half_true_modif_m`, `s_mutants_16`, `dillig02_m`).
/// 3 s is the advertised Kind pre-pass budget in `adaptive_multi_pred.rs`
/// and keeps the pre-strategy consistent with other portfolio stages.
pub(crate) const ALGEBRAIC_PRESTAGE_BUDGET: Duration = Duration::from_secs(3);
pub(crate) const ALGEBRAIC_POLYNOMIAL_PRESTAGE_BUDGET_CAP: Duration = Duration::from_secs(10);
pub(crate) const ALGEBRAIC_LARGE_ACYCLIC_BUDGET: Duration = Duration::from_secs(30);
const ALGEBRAIC_LARGE_ACYCLIC_MIN_PREDS: usize = 80;
const ALGEBRAIC_LARGE_ACYCLIC_MIN_DEPTH: usize = 80;

pub(crate) fn algebraic_prestage_budget(
    features: &ProblemFeatures,
    solve_budget: Duration,
) -> Duration {
    let mut budget = ALGEBRAIC_PRESTAGE_BUDGET;

    // Polynomial closed-form synthesis is the intended route for accumulator
    // and s_multipl-style LIA benchmarks. Give pure arithmetic cases more than
    // the default 3s, but cap the extension so arbitrary Int multiplication
    // does not monopolize CHC-COMP wall time before the rest of the portfolio.
    if !solve_budget.is_zero()
        && features.has_multiplication
        && !features.has_mod_div
        && !features.uses_arrays
        && !features.uses_real
    {
        let polynomial_budget = solve_budget
            .div_f64(2.0)
            .min(ALGEBRAIC_POLYNOMIAL_PRESTAGE_BUDGET_CAP);
        budget = budget.max(polynomial_budget);
    }

    // Large acyclic compiler block graphs can require many exact fact
    // transfers before the algebraic proof reaches the query edge (#9004,
    // model-checker-consumer vec-iterator canaries).
    // Keep the strict 3s default for hard nonlinear/modular cases, but allow
    // this bounded linear DAG shape enough time to finish its constructive proof.
    if matches!(features.class, ProblemClass::MultiPredLinear)
        && features.is_linear
        && !features.has_cycles
        && features.has_multiplication
        && !features.has_mod_div
        && !features.uses_arrays
        && !features.uses_real
        && features.num_predicates >= ALGEBRAIC_LARGE_ACYCLIC_MIN_PREDS
        && features.dag_depth >= ALGEBRAIC_LARGE_ACYCLIC_MIN_DEPTH
    {
        budget = ALGEBRAIC_LARGE_ACYCLIC_BUDGET;
    }

    if !solve_budget.is_zero() {
        let half_budget = solve_budget.div_f64(2.0);
        if half_budget < budget {
            // Honour the half-budget cap. Re-raising to ALGEBRAIC_PRESTAGE_BUDGET
            // here defeated the very cap being applied: at a 5s wall the 3s floor
            // handed this pre-stage 63% of the budget before any engine ran. The
            // floor only ever bound for solve budgets under 6s, so competition
            // budgets are unaffected.
            budget = half_budget;
        }
        budget = budget.min(solve_budget);
    }

    budget
}
