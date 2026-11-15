// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Producer-side ownership of the structural-array progress and unit channel.

use super::*;

#[cfg(test)]
mod tests;

impl Executor {
    /// Discovery, preparation and every recording round consume this ONE
    /// closure. Moving it into the preprocessor does not reset the envelope.
    pub(in crate::executor) fn array_preprocessing_progress(
        &self,
    ) -> Box<dyn FnMut(usize, usize) -> bool> {
        let budget = ArrayReplayBudget::new(self);
        Box::new(move |work, bytes| budget.charge(work, bytes))
    }

    /// Retain checked proof data separately from the stamped rewrite ledger.
    /// The caller changes working assertions only AFTER this returns true;
    /// those changes must be infallible ownership moves, not another check.
    pub(in crate::executor) fn retain_array_preprocessing_units(
        &mut self,
        units: Vec<ArrayUnitDerivation>,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> bool {
        if !crate::quant_unit_authority::quant_unit_authority_enabled() {
            return false;
        }
        let stored = &mut self.propagated_value_provenance.array_units;
        let Some(count) = stored.len().checked_add(units.len()) else {
            return false;
        };
        let Some(bytes) = count.checked_mul(std::mem::size_of::<ArrayUnitDerivation>()) else {
            return false;
        };
        if count > MAX_STORED_PROPAGATION_RECORDS
            || !progress(count, bytes)
            || stored.try_reserve_exact(units.len()).is_err()
            || !progress(0, 0)
        {
            return false;
        }
        stored.extend(units);
        true
    }
}
