// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Terminal checked-extraction transport, not an owned native solve.
//!
//! Only the two concrete callback result types below are accepted. The legacy
//! callback is moved unchanged; the fallible callback retains its original
//! error. No owner, grant, retry, polling sink, or payload copy is created.
//! Caller preparation, callback work, stale payload disposal and all native
//! solving remain outside this component's resource accounting.

use ay_core::original_query::QueryError;

use super::TheoryModels;
use crate::executor_types::ExecutorError;
use crate::Executor;

pub(in crate::executor) trait ModelExtractionResult {
    fn into_model_extraction_result(self) -> Result<TheoryModels, QueryError>;
}

impl ModelExtractionResult for TheoryModels {
    fn into_model_extraction_result(self) -> Result<TheoryModels, QueryError> {
        Ok(self)
    }
}

impl ModelExtractionResult for Result<TheoryModels, QueryError> {
    fn into_model_extraction_result(self) -> Result<TheoryModels, QueryError> {
        self
    }
}

pub(in crate::executor) fn model_extraction_result(
    result: impl ModelExtractionResult,
) -> Result<TheoryModels, QueryError> {
    result.into_model_extraction_result()
}

impl Executor {
    /// Retire provisional query artefacts, without turning a refused extraction
    /// into a retryable candidate verdict. Call only after arm-specific cleanup.
    ///
    /// This reuses ordinary lifecycle invalidation and leaves incremental SAT/
    /// theory state to the caller's existing epilogue. Previously exported
    /// completed facts are not revoked or retroactively reinterpreted.
    pub(in crate::executor) fn terminal_model_extraction_error(
        &mut self,
        error: QueryError,
    ) -> ExecutorError {
        self.invalidate_last_check_result();
        self.clear_dt_theory_model();
        ExecutorError::ModelExtraction(error)
    }
}

#[cfg(test)]
mod tests;
