// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Composition of prepared interpretation DATA, not native model publication.

use super::combiner::TheoryCombiner;
use ay_arrays::ArrayModel;
use ay_core::original_query::{QueryError, WorkBudget};
use ay_core::TermId;
use ay_euf::EufModel;

#[cfg(test)]
mod tests;

impl TheoryCombiner<'_> {
    /// Compose prepared Bool/BV/flat-array extraction on ONE borrowed ledger.
    ///
    /// The EUF root inventory supplies the borrowed term-value map to arrays.
    /// No cache preparation, model fixup, map clone, grant or native solve runs.
    /// Arithmetic combiners and missing arrays terminally refuse; both prepared
    /// extractors retain their own complete cohort/state checks. Output is
    /// ordinary caller-owned DATA, with no publication or later-use authority.
    pub(crate) fn try_extract_prepared_euf_array_models_with_budget(
        &self,
        roots: &[TermId],
        work: &mut WorkBudget<'_>,
    ) -> Result<(EufModel, ArrayModel), QueryError> {
        // Prepay the fixed branches and all tuple/header moves/disposal BEFORE
        // source inspection. Nested partial-output disposal was prepaid by the
        // two producers' actual string/vector/table construction offers.
        let bytes = std::mem::size_of::<(EufModel, ArrayModel)>()
            .checked_mul(8)
            .ok_or_else(|| work.refuse_exhaustion())?;
        work.admit(128, bytes)?;
        let result = (|| {
            if self.lia.is_some() || self.lra.is_some() {
                return Err(work.refuse_exhaustion());
            }
            let arrays = self
                .arrays
                .as_ref()
                .ok_or_else(|| work.refuse_exhaustion())?;
            let euf = self
                .euf
                .try_extract_prepared_bv_model_from_roots_with_budget(roots, work)?;
            match arrays.try_extract_prepared_flat_model_with_budget(&euf.term_values, work) {
                Ok(array) => Ok((euf, array)),
                Err(error) => {
                    drop(euf);
                    Err(error)
                }
            }
        })();
        finish(result, work)
    }
}

fn finish(
    result: Result<(EufModel, ArrayModel), QueryError>,
    work: &mut WorkBudget<'_>,
) -> Result<(EufModel, ArrayModel), QueryError> {
    match result {
        Err(error) => {
            let _ = work.charge(0);
            Err(error)
        }
        Ok(models) => match work.charge(0) {
            Ok(()) => Ok(models),
            Err(error) => {
                drop(models);
                let _ = work.charge(0);
                Err(error)
            }
        },
    }
}
