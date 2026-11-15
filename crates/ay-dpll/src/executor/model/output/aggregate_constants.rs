// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One aggregate-constant emission priority for both public output commands.

use super::{Executor, Model, Sort, TermId};
use std::collections::HashMap;

pub(super) enum AggregateConstantValue {
    Value(String),
    Absent,
    Poisoned,
}

/// Query-local reconstruction only: never cached across models, source changes
/// or evaluation attempts. The map contains only the existing independent
/// evaluator's complete declared-constant values and admitted aggregate reads,
/// not raw constructor printing.
#[derive(Default)]
pub(super) struct AggregateConstantValues {
    gate: HashMap<TermId, String>,
}

impl AggregateConstantValues {
    pub(super) fn collect(exec: &Executor, model: &Model) -> Result<Self, String> {
        exec.check_evaluation_read()?;
        let gate = if model.has_residual_arrays() {
            // A residual owner is terminal on a missing/stale value. An
            // omission-based map must never license a competing fallback.
            HashMap::new()
        } else {
            exec.gate_emit_reconstructions(model)
                .map_err(|origin| format!("aggregate reconstruction query refused: {origin:?}"))?
        };
        exec.check_evaluation_read()?;
        Ok(Self { gate })
    }

    pub(super) fn for_values(
        exec: &Executor,
        model: &Model,
        requested: &[(String, TermId)],
    ) -> Result<Self, String> {
        // Ordinary scalar batches retain their path. Exact scalar projections
        // through array-bearing records need the independent aggregate reader.
        let mut include_constants = false;
        for (_, term) in requested {
            exec.check_evaluation_read()?;
            if aggregate_sort(exec, *term)? {
                include_constants = true;
            }
        }
        let mut values = if include_constants {
            Self::collect(exec, model)?
        } else {
            Self::default()
        };
        let reads = exec.independent_aggregate_read_values(model, requested)?;
        values.gate.try_reserve(reads.len()).map_err(|_| {
            exec.record_evaluation_stop(
                crate::executor_types::UnknownOrigin::DeterministicResourceBudget,
            );
            "aggregate model query allocation refused".to_string()
        })?;
        values.gate.extend(reads);
        exec.check_evaluation_read()?;
        Ok(values)
    }

    pub(super) fn resolve(
        &self,
        exec: &Executor,
        model: &Model,
        term: TermId,
    ) -> Result<AggregateConstantValue, String> {
        exec.check_evaluation_read()?;
        let value = self.resolve_unstopped(exec, model, term)?;
        exec.check_evaluation_read()?;
        Ok(value)
    }

    fn resolve_unstopped(
        &self,
        exec: &Executor,
        model: &Model,
        term: TermId,
    ) -> Result<AggregateConstantValue, String> {
        if !aggregate_sort(exec, term)? {
            return Ok(match self.gate.get(&term) {
                Some(value) => AggregateConstantValue::Value(value.clone()),
                None => AggregateConstantValue::Absent,
            });
        }
        let sort = exec.ctx.terms.sort(term);
        match exec.completed_model_value(model, term) {
            Ok(Some(value)) => {
                return exec
                    .format_gate_model_value(&value, sort)
                    .map(AggregateConstantValue::Value)
                    .ok_or_else(|| "completed model value cannot be rendered exactly".to_string());
            }
            Ok(None) => {}
            Err(()) => return Err("retained array model value is unavailable".to_string()),
        }
        // Keep the per-term renderer's projection priority. A checked total
        // projection is not permission to read a competing UF/e-graph leaf.
        let term = match model
            .projection_ufs
            .peel_application_chain(&exec.ctx.terms, term)
        {
            Ok(Some(projected)) => projected,
            Ok(None) => term,
            Err(error) => return Err(error.to_string()),
        };
        let sort = exec.ctx.terms.sort(term);
        if exec.datatype_sort_name(sort).is_some() {
            // Selector totalizations commit branch keys from this assignment:
            // printed constants must use that same value, even when the gate
            // has another complete reconstruction. A proven disequality
            // collision must not escape through that map or a legacy default.
            if let Some(value) = exec.dt_egraph_value(model, term) {
                return Ok(AggregateConstantValue::Value(value));
            }
            if exec.dt_egraph_class_poisoned(model, term) {
                return Ok(AggregateConstantValue::Poisoned);
            }
        }
        Ok(match self.gate.get(&term) {
            Some(value) => AggregateConstantValue::Value(value.clone()),
            None => AggregateConstantValue::Absent,
        })
    }
}

fn aggregate_sort(exec: &Executor, term: TermId) -> Result<bool, String> {
    if exec.ctx.terms.entry_stamp(term).is_none() {
        return Err("model value term is not live".to_string());
    }
    let sort = exec.ctx.terms.sort(term);
    Ok(matches!(sort, Sort::Array(_)) || exec.datatype_sort_name(sort).is_some())
}

#[cfg(test)]
mod tests;
