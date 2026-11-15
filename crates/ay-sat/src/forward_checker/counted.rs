// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Count only bootstrap here; subsequent DRUP operations remain separate work.

use super::ForwardChecker;
use ay_core::original_query::{CountedAdmission, CountedAdmissionError, QueryError};
use ay_drat_check::checker::{CheckerConstructionError, DratChecker};

impl ForwardChecker {
    pub(crate) fn try_new_counted(
        num_vars: usize,
        sample_period: u64,
        owner: &CountedAdmission,
    ) -> Result<Self, CountedAdmissionError> {
        // with_work catches observer/operation unwind and fences cleanup. Its
        // adapter shares the same ledger; it grants no additional work.
        let result = owner.with_work(|_| {
            let inner = DratChecker::try_new_drup_with_admission(num_vars, &mut |work, bytes| {
                owner.admit(work, bytes)
            });
            Ok(inner
                .map(|inner| Self::from_inner(inner, sample_period))
                .map_err(|error| owner.refuse(construction_error(error))))
        })?;
        // Failed construction already destroyed partial buffers before the
        // precise cause was latched. Successful callback-local cleanup also
        // precedes this fence; no observer is owned by the returned checker.
        owner.check()?;
        result
    }
}

fn construction_error(
    error: CheckerConstructionError<CountedAdmissionError>,
) -> CountedAdmissionError {
    match error {
        CheckerConstructionError::Admission(error) => error,
        CheckerConstructionError::VariableLimit { .. }
        | CheckerConstructionError::SizeOverflow
        | CheckerConstructionError::Allocation(_) => {
            CountedAdmissionError::Original(QueryError::Exhausted.into())
        }
    }
}

#[cfg(test)]
mod tests;
