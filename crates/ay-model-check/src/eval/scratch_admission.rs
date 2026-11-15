// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrow the existing evaluator ledger for native scratch-buffer utilities.
//! This creates no allowance, source permission or machine reservation. The
//! opaque construction error is only transport; the evaluator itself retains
//! the original refusal and restores it after the algorithm has returned.

use super::*;
use ay_core::original_query::{CountedAdmissionError, OriginalAdmissionError};
use ay_core::term::TermConstructionAdmission;

pub(super) struct ScratchAdmission<'a, 'model> {
    evaluator: &'a Evaluator<'model>,
}

impl<'a, 'model> ScratchAdmission<'a, 'model> {
    pub(super) fn new(evaluator: &'a Evaluator<'model>) -> Self {
        Self { evaluator }
    }

    pub(super) fn finish<T>(&self, result: EvalResult<T>) -> EvalResult<T> {
        self.evaluator.admit_evaluation(0, 0).and(result)
    }
}

impl TermConstructionAdmission for ScratchAdmission<'_, '_> {
    fn admit(&self, work: usize, storage: usize) -> Result<(), CountedAdmissionError> {
        self.evaluator
            .admit_evaluation(work, storage)
            .map_err(|_| OriginalAdmissionError::ObserverStopped.into())
    }

    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        let _ = self.evaluator.admission_error(error.to_string());
        error
    }
}
