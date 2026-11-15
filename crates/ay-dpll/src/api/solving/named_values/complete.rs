// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! A complete batch from one read and the same immutable accepted native model.

use crate::api::CompleteModelValue;

use super::*;

impl Solver {
    /// Retrieve complete interpretations for exact live source constants.
    ///
    /// Input order and duplicate names are preserved. All names and recursive
    /// declared sorts are admitted together through the unchanged exact-source
    /// lookup. Functional arrays come directly from the installed native model,
    /// authenticated against its source, query roots and entry stamps; lambda
    /// text is neither parsed nor replaced by finite samples. All ordinary
    /// literal values share ONE existing cumulative typed decoder.
    ///
    /// The whole batch uses one model-evaluation read and accepted-SAT checks
    /// before and after extraction. Native snapshots debit the installed
    /// functional model's original work owner; request/sort admission and
    /// literal decoding retain their separate existing per-batch allowances.
    /// Missing, stale, unsupported, ill-sorted or stopped data refuses the
    /// whole batch, never a per-value fallback. No model or fresh allowance is
    /// constructed. Native printing and opaque allocator/RSS costs are not
    /// bounded by the existing typed decoder's logical allowances.
    ///
    /// Returned data is not a SAT capability or a checked witness. Retain the
    /// originating solve evidence and independently replay the source witness.
    /// The legacy literal-only `try_get_named_values` API is unchanged.
    #[must_use = "complete model extraction can refuse the entire batch"]
    pub fn try_get_named_values_complete(
        &self,
        names: &[&str],
    ) -> Result<Vec<CompleteModelValue>, SolverError> {
        self.with_model_evaluation_read(|| {
            self.ensure_last_sat_model_accepted_for_consumer()?;
            self.executor
                .check_evaluation_read()
                .map_err(SolverError::ModelGenerationFailed)?;
            let result = self.complete_named_values_in_read(names)?;
            self.ensure_last_sat_model_accepted_for_consumer()?;
            self.executor
                .check_evaluation_read()
                .map_err(SolverError::ModelGenerationFailed)?;
            Ok(result)
        })
    }

    fn complete_named_values_in_read(
        &self,
        names: &[&str],
    ) -> Result<Vec<CompleteModelValue>, SolverError> {
        let requests = self.named_value_requests(names)?;
        if requests.is_empty() {
            return Ok(Vec::new());
        }
        let mut terms = Vec::new();
        self.complete_value_reserve(&mut terms, requests.len())?;
        terms.extend(requests.iter().map(|(_, term)| *term));
        let snapshots = self
            .executor
            .functional_array_snapshots_for_named_values(&terms)
            .map_err(SolverError::ModelGenerationFailed)?;
        if snapshots.len() != requests.len() {
            return Err(complete_error("native snapshot batch length mismatch"));
        }
        let mut literals = Vec::new();
        self.complete_value_reserve(&mut literals, requests.len())?;
        for (request, snapshot) in requests.into_iter().zip(&snapshots) {
            if snapshot.is_none() {
                literals.push(request);
            }
        }
        let values = self.complete_literal_values(&literals)?;
        let mut values = values.into_iter();
        let mut result = Vec::new();
        self.complete_value_reserve(&mut result, names.len())?;
        for snapshot in snapshots {
            let value = match snapshot {
                Some(value) => CompleteModelValue::FunctionalArray(value),
                None => CompleteModelValue::Literal(
                    values
                        .next()
                        .ok_or_else(|| complete_error("literal batch length mismatch"))?,
                ),
            };
            result.push(value);
        }
        if values.next().is_some() {
            return Err(complete_error("literal batch contains extra values"));
        }
        Ok(result)
    }

    fn complete_literal_values(
        &self,
        requests: &[(String, TermId)],
    ) -> Result<Vec<ModelValue>, SolverError> {
        if requests.is_empty() {
            return Ok(Vec::new());
        }
        self.executor
            .check_evaluation_read()
            .map_err(SolverError::ModelGenerationFailed)?;
        let output = self.executor.values_for_decoder(requests);
        let result = model_parse::parse_get_value_output(
            &output,
            requests,
            self.terms(),
            self.executor.context(),
        );
        drop(output);
        self.executor
            .check_evaluation_read()
            .map_err(SolverError::ModelGenerationFailed)?;
        result.ok_or_else(|| {
            complete_error(
                "complete literal output is unavailable, malformed, ill-sorted or over budget",
            )
        })
    }

    fn complete_value_reserve<T>(
        &self,
        values: &mut Vec<T>,
        count: usize,
    ) -> Result<(), SolverError> {
        values.try_reserve_exact(count).map_err(|_| {
            SolverError::ModelGenerationFailed(
                self.executor.complete_named_value_allocation_refused(),
            )
        })
    }
}

fn complete_error(message: &str) -> SolverError {
    SolverError::ModelGenerationFailed(message.to_owned())
}

#[cfg(test)]
mod tests;
