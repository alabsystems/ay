// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

use ay_dpll::api::SolverError;
use ay_dpll::api::Term;

use super::context::ExecutionContext;
use super::types::ExecuteValueMap;
use super::ModelValue;

pub(super) fn render_model_values(values: ExecuteValueMap<ModelValue>) -> ExecuteValueMap<String> {
    values
        .into_iter()
        .map(|(name, value)| (name, value.to_string()))
        .collect()
}

/// Extract model from solver after SAT result.
pub(super) fn extract_model_typed(
    ctx: &ExecutionContext,
) -> Result<ExecuteValueMap<ModelValue>, SolverError> {
    ctx.solver.try_get_model_map()
}

/// Extract get-value results from solver after SAT (#1977).
///
/// Evaluates all terms collected from GetValue constraints and returns
/// typed values keyed by expression string.
pub(super) fn extract_get_values_typed(
    ctx: &ExecutionContext,
) -> Result<ExecuteValueMap<ModelValue>, SolverError> {
    extract_get_values_from_terms_typed(ctx, &ctx.get_value_terms)
}

pub(super) fn extract_get_values_from_terms_typed(
    ctx: &ExecutionContext,
    terms: &[(String, Term)],
) -> Result<ExecuteValueMap<ModelValue>, SolverError> {
    if terms.is_empty() {
        return Ok(ExecuteValueMap::default());
    }

    // Collect just the terms for batch evaluation
    let translated_terms = terms.iter().map(|(_, t)| t.clone()).collect::<Vec<_>>();

    let model_values = ctx.solver.try_get_values(&translated_terms)?;
    let mut values = ay_core::kani_compat::det_hash_map_with_capacity(model_values.len());
    for ((expr_str, _), model_value) in terms.iter().zip(model_values.into_iter()) {
        values.insert(expr_str.clone(), model_value);
    }
    Ok(values)
}
